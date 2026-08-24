import NAR4C077C001Part015

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

noncomputable def nb077_split_alpha_0005 (x : Var) (F : Class) (I : Class) : TAlphaWff [((nb077_alpha_dummy_137 F I), (nb077_alpha_dummy_138 x)), ((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_137 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))) (Wff.neg (Wff.classMem (Class.cv (nb077_alpha_dummy_137 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I)))))) (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_138 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))) (Wff.neg (Wff.classMem (Class.cv (nb077_alpha_dummy_138 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0096 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0097 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0096 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0097 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0126 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0127 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0124 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0125 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_104 F I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_106 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0100 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0101 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0100 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0101 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0098 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0099 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I), (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)), ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_137 F I), (nb077_alpha_dummy_138 x)), ((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c) (nb077_wpp_refl_0019 x F I))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0104 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0105 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0102 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0103 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0108 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0109 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0106 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0107 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0104 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0105 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0102 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0103 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0108 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0109 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0106 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0107 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I), (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)), ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_137 F I), (nb077_alpha_dummy_138 x)), ((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0) (nb077_wpp_refl_0020 x F I))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0112 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0113 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0110 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0111 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0112 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0113 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0110 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0111 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0116 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0117 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0114 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0115 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0116 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0117 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0114 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0115 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0098 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0099 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_137 F I), (nb077_alpha_dummy_138 x)), ((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0021 x F I))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0098 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0099 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0098 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0099 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_137 F I), (nb077_alpha_dummy_138 x)), ((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0021 x F I)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0096 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0097 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0096 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0097 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0126 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0127 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0124 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0125 x) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_104 F I))).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_106 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0100 F I) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0101 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0100 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0101 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0098 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0099 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I), (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)), ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_137 F I), (nb077_alpha_dummy_138 x)), ((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c1c) (nb077_wpp_refl_0019 x F I))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0104 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0105 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0102 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0103 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0108 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0109 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0106 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0107 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0104 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0105 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0102 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0103 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0108 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0109 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0106 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0107 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I), (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)), ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_137 F I), (nb077_alpha_dummy_138 x)), ((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_c0) (nb077_wpp_refl_0020 x F I))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0112 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0113 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0110 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0111 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0112 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0113 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0110 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0111 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_111 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_113 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0116 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0117 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0114 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0115 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0116 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0117 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0114 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0115 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0098 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0099 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_137 F I), (nb077_alpha_dummy_138 x)), ((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0021 x F I))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0098 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0099 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0098 F I) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0099 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_137 F I), (nb077_alpha_dummy_138 x)), ((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] (syn_cnnc) (nb077_wpp_refl_0021 x F I))))))))))))))))))))

theorem nb077_wpp_notmem_0348 (F : Class) (I : Class) : (nb077_alpha_dummy_135 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_135, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0104 F I)

theorem nb077_wpp_notmem_0349 (x : Var) : (nb077_alpha_dummy_136 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_136, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0105 x)

theorem nb077_wpp_notmem_0350 (F : Class) (I : Class) : (nb077_alpha_dummy_104 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_104, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0092 F I)

theorem nb077_wpp_notmem_0351 (x : Var) : (nb077_alpha_dummy_106 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_106, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0093 x)

theorem nb077_wpp_notmem_0352 (F : Class) (I : Class) : (nb077_alpha_dummy_103 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_103, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0094 F I)

theorem nb077_wpp_notmem_0353 (x : Var) : (nb077_alpha_dummy_105 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_105, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0095 x)

theorem nb077_wpp_notmem_0354 (F : Class) (I : Class) : (nb077_alpha_dummy_133 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_133, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0106 F I)

theorem nb077_wpp_notmem_0355 (x : Var) : (nb077_alpha_dummy_134 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_134, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0107 x)

theorem nb077_wpp_notmem_0356 (F : Class) (I : Class) : (nb077_alpha_dummy_107 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_107, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0098 F I)

theorem nb077_wpp_notmem_0357 (x : Var) : (nb077_alpha_dummy_108 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_108, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0099 x)

theorem nb077_wpp_notmem_0358 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_061, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0100 F I)

theorem nb077_wpp_notmem_0359 (x : Var) : (nb077_alpha_dummy_064 x) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb077_alpha_dummy_064, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb077_compact_fv_empty_0101 x)

theorem nb077_compact_envfresh_0022 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_135 F I) (nb077_alpha_dummy_136 x) (nb077_wpp_notmem_0348 F I) (nb077_wpp_notmem_0349 x) (TEnvFresh.consFresh (nb077_alpha_dummy_104 F I) (nb077_alpha_dummy_106 x) (nb077_wpp_notmem_0350 F I) (nb077_wpp_notmem_0351 x) (TEnvFresh.consFresh (nb077_alpha_dummy_103 F I) (nb077_alpha_dummy_105 x) (nb077_wpp_notmem_0352 F I) (nb077_wpp_notmem_0353 x) (TEnvFresh.consFresh (nb077_alpha_dummy_133 F I) (nb077_alpha_dummy_134 x) (nb077_wpp_notmem_0354 F I) (nb077_wpp_notmem_0355 x) (TEnvFresh.consFresh (nb077_alpha_dummy_107 F I) (nb077_alpha_dummy_108 x) (nb077_wpp_notmem_0356 F I) (nb077_wpp_notmem_0357 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0358 F I) (nb077_wpp_notmem_0359 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0260 F I) (nb077_wpp_notmem_0261 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0262 F I) (nb077_wpp_notmem_0263 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0264 F I) (nb077_wpp_notmem_0265 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0266 F I) (nb077_wpp_notmem_0267 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0268 F I) (nb077_wpp_notmem_0269 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0134 F I) (nb077_wpp_notmem_0135 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0136 F I) (nb077_wpp_notmem_0137 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0138 F I) (nb077_wpp_notmem_0139 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0140 F I) (nb077_wpp_notmem_0141 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0142 F I) (nb077_wpp_notmem_0143 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0144 F I) (nb077_wpp_notmem_0145 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0146 F I) (nb077_wpp_notmem_0147 x F I) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))))))

noncomputable def nb077_wpp_refl_0022 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_135 F I), (nb077_alpha_dummy_136 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_133 F I), (nb077_alpha_dummy_134 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0022 x F I)

theorem nb077_compact_fv_empty_0108 (F : Class) (I : Class) : (nb077_alpha_dummy_163 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0360 (F : Class) (I : Class) : (nb077_alpha_dummy_163 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_163, fv_syn_c1c] using (nb077_compact_fv_empty_0108 F I)

theorem nb077_compact_fv_empty_0109 (x : Var) : (nb077_alpha_dummy_166 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0361 (x : Var) : (nb077_alpha_dummy_166 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_166, fv_syn_c1c] using (nb077_compact_fv_empty_0109 x)

theorem nb077_compact_fv_empty_0110 (F : Class) (I : Class) : (nb077_alpha_dummy_162 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0362 (F : Class) (I : Class) : (nb077_alpha_dummy_162 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_162, fv_syn_c1c] using (nb077_compact_fv_empty_0110 F I)

theorem nb077_compact_fv_empty_0111 (x : Var) : (nb077_alpha_dummy_165 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0363 (x : Var) : (nb077_alpha_dummy_165 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_165, fv_syn_c1c] using (nb077_compact_fv_empty_0111 x)

theorem nb077_compact_fv_empty_0112 (F : Class) (I : Class) : (nb077_alpha_dummy_161 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0364 (F : Class) (I : Class) : (nb077_alpha_dummy_161 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_161, fv_syn_c1c] using (nb077_compact_fv_empty_0112 F I)

theorem nb077_compact_fv_empty_0113 (x : Var) : (nb077_alpha_dummy_164 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0365 (x : Var) : (nb077_alpha_dummy_164 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_164, fv_syn_c1c] using (nb077_compact_fv_empty_0113 x)

theorem nb077_compact_fv_empty_0114 (F : Class) (I : Class) : (nb077_alpha_dummy_159 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0366 (F : Class) (I : Class) : (nb077_alpha_dummy_159 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_159, fv_syn_c1c] using (nb077_compact_fv_empty_0114 F I)

theorem nb077_compact_fv_empty_0115 (x : Var) : (nb077_alpha_dummy_160 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0367 (x : Var) : (nb077_alpha_dummy_160 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_160, fv_syn_c1c] using (nb077_compact_fv_empty_0115 x)

theorem nb077_compact_fv_empty_0116 (F : Class) (I : Class) : (nb077_alpha_dummy_155 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0368 (F : Class) (I : Class) : (nb077_alpha_dummy_155 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_155, fv_syn_c1c] using (nb077_compact_fv_empty_0116 F I)

theorem nb077_compact_fv_empty_0117 (x : Var) : (nb077_alpha_dummy_157 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0369 (x : Var) : (nb077_alpha_dummy_157 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_157, fv_syn_c1c] using (nb077_compact_fv_empty_0117 x)

theorem nb077_compact_fv_empty_0118 (F : Class) (I : Class) : (nb077_alpha_dummy_156 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0370 (F : Class) (I : Class) : (nb077_alpha_dummy_156 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_156, fv_syn_c1c] using (nb077_compact_fv_empty_0118 F I)

theorem nb077_compact_fv_empty_0119 (x : Var) : (nb077_alpha_dummy_158 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0371 (x : Var) : (nb077_alpha_dummy_158 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_158, fv_syn_c1c] using (nb077_compact_fv_empty_0119 x)

theorem nb077_compact_fv_empty_0120 (F : Class) (I : Class) : (nb077_alpha_dummy_148 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0372 (F : Class) (I : Class) : (nb077_alpha_dummy_148 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_148, fv_syn_c1c] using (nb077_compact_fv_empty_0120 F I)

theorem nb077_compact_fv_empty_0121 (x : Var) : (nb077_alpha_dummy_150 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0373 (x : Var) : (nb077_alpha_dummy_150 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_150, fv_syn_c1c] using (nb077_compact_fv_empty_0121 x)

theorem nb077_compact_fv_empty_0122 (F : Class) (I : Class) : (nb077_alpha_dummy_147 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0374 (F : Class) (I : Class) : (nb077_alpha_dummy_147 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_147, fv_syn_c1c] using (nb077_compact_fv_empty_0122 F I)

theorem nb077_compact_fv_empty_0123 (x : Var) : (nb077_alpha_dummy_149 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0375 (x : Var) : (nb077_alpha_dummy_149 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_149, fv_syn_c1c] using (nb077_compact_fv_empty_0123 x)

theorem nb077_compact_fv_empty_0124 (F : Class) (I : Class) : (nb077_alpha_dummy_153 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0376 (F : Class) (I : Class) : (nb077_alpha_dummy_153 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_153, fv_syn_c1c] using (nb077_compact_fv_empty_0124 F I)

theorem nb077_compact_fv_empty_0125 (x : Var) : (nb077_alpha_dummy_154 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0377 (x : Var) : (nb077_alpha_dummy_154 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_154, fv_syn_c1c] using (nb077_compact_fv_empty_0125 x)

theorem nb077_compact_fv_empty_0126 (F : Class) (I : Class) : (nb077_alpha_dummy_151 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0378 (F : Class) (I : Class) : (nb077_alpha_dummy_151 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_151, fv_syn_c1c] using (nb077_compact_fv_empty_0126 F I)

theorem nb077_compact_fv_empty_0127 (x : Var) : (nb077_alpha_dummy_152 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0379 (x : Var) : (nb077_alpha_dummy_152 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_152, fv_syn_c1c] using (nb077_compact_fv_empty_0127 x)

theorem nb077_compact_fv_empty_0128 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0380 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_140, fv_syn_c1c] using (nb077_compact_fv_empty_0128 F I)

theorem nb077_compact_fv_empty_0129 (x : Var) : (nb077_alpha_dummy_143 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0381 (x : Var) : (nb077_alpha_dummy_143 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_143, fv_syn_c1c] using (nb077_compact_fv_empty_0129 x)

theorem nb077_compact_fv_empty_0130 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0382 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_139, fv_syn_c1c] using (nb077_compact_fv_empty_0130 F I)

theorem nb077_compact_fv_empty_0131 (x : Var) : (nb077_alpha_dummy_142 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0383 (x : Var) : (nb077_alpha_dummy_142 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_142, fv_syn_c1c] using (nb077_compact_fv_empty_0131 x)

theorem nb077_compact_fv_empty_0132 (F : Class) (I : Class) : (nb077_alpha_dummy_145 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0384 (F : Class) (I : Class) : (nb077_alpha_dummy_145 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_145, fv_syn_c1c] using (nb077_compact_fv_empty_0132 F I)

theorem nb077_compact_fv_empty_0133 (x : Var) : (nb077_alpha_dummy_146 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0385 (x : Var) : (nb077_alpha_dummy_146 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_146, fv_syn_c1c] using (nb077_compact_fv_empty_0133 x)

theorem nb077_compact_envfresh_0023 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_163 F I), (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I), (nb077_alpha_dummy_165 x)), ((nb077_alpha_dummy_161 F I), (nb077_alpha_dummy_164 x)), ((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)), ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_153 F I), (nb077_alpha_dummy_154 x)), ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_163 F I) (nb077_alpha_dummy_166 x) (nb077_wpp_notmem_0360 F I) (nb077_wpp_notmem_0361 x) (TEnvFresh.consFresh (nb077_alpha_dummy_162 F I) (nb077_alpha_dummy_165 x) (nb077_wpp_notmem_0362 F I) (nb077_wpp_notmem_0363 x) (TEnvFresh.consFresh (nb077_alpha_dummy_161 F I) (nb077_alpha_dummy_164 x) (nb077_wpp_notmem_0364 F I) (nb077_wpp_notmem_0365 x) (TEnvFresh.consFresh (nb077_alpha_dummy_159 F I) (nb077_alpha_dummy_160 x) (nb077_wpp_notmem_0366 F I) (nb077_wpp_notmem_0367 x) (TEnvFresh.consFresh (nb077_alpha_dummy_155 F I) (nb077_alpha_dummy_157 x) (nb077_wpp_notmem_0368 F I) (nb077_wpp_notmem_0369 x) (TEnvFresh.consFresh (nb077_alpha_dummy_156 F I) (nb077_alpha_dummy_158 x) (nb077_wpp_notmem_0370 F I) (nb077_wpp_notmem_0371 x) (TEnvFresh.consFresh (nb077_alpha_dummy_148 F I) (nb077_alpha_dummy_150 x) (nb077_wpp_notmem_0372 F I) (nb077_wpp_notmem_0373 x) (TEnvFresh.consFresh (nb077_alpha_dummy_147 F I) (nb077_alpha_dummy_149 x) (nb077_wpp_notmem_0374 F I) (nb077_wpp_notmem_0375 x) (TEnvFresh.consFresh (nb077_alpha_dummy_153 F I) (nb077_alpha_dummy_154 x) (nb077_wpp_notmem_0376 F I) (nb077_wpp_notmem_0377 x) (TEnvFresh.consFresh (nb077_alpha_dummy_151 F I) (nb077_alpha_dummy_152 x) (nb077_wpp_notmem_0378 F I) (nb077_wpp_notmem_0379 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0380 F I) (nb077_wpp_notmem_0381 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0382 F I) (nb077_wpp_notmem_0383 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0384 F I) (nb077_wpp_notmem_0385 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0290 F I) (nb077_wpp_notmem_0291 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0168 F I) (nb077_wpp_notmem_0169 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0170 F I) (nb077_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0172 F I) (nb077_wpp_notmem_0173 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0174 F I) (nb077_wpp_notmem_0175 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0176 F I) (nb077_wpp_notmem_0177 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0030 F I) (nb077_wpp_notmem_0031 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0032 F I) (nb077_wpp_notmem_0033 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0034 F I) (nb077_wpp_notmem_0035 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0036 F I) (nb077_wpp_notmem_0037 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0038 F I) (nb077_wpp_notmem_0039 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0040 F I) (nb077_wpp_notmem_0041 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0042 F I) (nb077_wpp_notmem_0043 x F I) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0023 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_163 F I), (nb077_alpha_dummy_166 x)), ((nb077_alpha_dummy_162 F I), (nb077_alpha_dummy_165 x)), ((nb077_alpha_dummy_161 F I), (nb077_alpha_dummy_164 x)), ((nb077_alpha_dummy_159 F I), (nb077_alpha_dummy_160 x)), ((nb077_alpha_dummy_155 F I), (nb077_alpha_dummy_157 x)), ((nb077_alpha_dummy_156 F I), (nb077_alpha_dummy_158 x)), ((nb077_alpha_dummy_148 F I), (nb077_alpha_dummy_150 x)), ((nb077_alpha_dummy_147 F I), (nb077_alpha_dummy_149 x)), ((nb077_alpha_dummy_153 F I), (nb077_alpha_dummy_154 x)), ((nb077_alpha_dummy_151 F I), (nb077_alpha_dummy_152 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0023 x F I)

theorem nb077_wpp_notmem_0386 (F : Class) (I : Class) : (nb077_alpha_dummy_163 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_163, fv_syn_c0] using (nb077_compact_fv_empty_0108 F I)

theorem nb077_wpp_notmem_0387 (x : Var) : (nb077_alpha_dummy_166 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_166, fv_syn_c0] using (nb077_compact_fv_empty_0109 x)

theorem nb077_wpp_notmem_0388 (F : Class) (I : Class) : (nb077_alpha_dummy_162 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_162, fv_syn_c0] using (nb077_compact_fv_empty_0110 F I)

theorem nb077_wpp_notmem_0389 (x : Var) : (nb077_alpha_dummy_165 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_165, fv_syn_c0] using (nb077_compact_fv_empty_0111 x)

theorem nb077_wpp_notmem_0390 (F : Class) (I : Class) : (nb077_alpha_dummy_161 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_161, fv_syn_c0] using (nb077_compact_fv_empty_0112 F I)

theorem nb077_wpp_notmem_0391 (x : Var) : (nb077_alpha_dummy_164 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_164, fv_syn_c0] using (nb077_compact_fv_empty_0113 x)

theorem nb077_wpp_notmem_0392 (F : Class) (I : Class) : (nb077_alpha_dummy_159 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_159, fv_syn_c0] using (nb077_compact_fv_empty_0114 F I)

theorem nb077_wpp_notmem_0393 (x : Var) : (nb077_alpha_dummy_160 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_160, fv_syn_c0] using (nb077_compact_fv_empty_0115 x)

theorem nb077_wpp_notmem_0394 (F : Class) (I : Class) : (nb077_alpha_dummy_155 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_155, fv_syn_c0] using (nb077_compact_fv_empty_0116 F I)

theorem nb077_wpp_notmem_0395 (x : Var) : (nb077_alpha_dummy_157 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_157, fv_syn_c0] using (nb077_compact_fv_empty_0117 x)

theorem nb077_wpp_notmem_0396 (F : Class) (I : Class) : (nb077_alpha_dummy_156 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_156, fv_syn_c0] using (nb077_compact_fv_empty_0118 F I)

theorem nb077_wpp_notmem_0397 (x : Var) : (nb077_alpha_dummy_158 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_158, fv_syn_c0] using (nb077_compact_fv_empty_0119 x)

theorem nb077_wpp_notmem_0398 (F : Class) (I : Class) : (nb077_alpha_dummy_148 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_148, fv_syn_c0] using (nb077_compact_fv_empty_0120 F I)

theorem nb077_wpp_notmem_0399 (x : Var) : (nb077_alpha_dummy_150 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_150, fv_syn_c0] using (nb077_compact_fv_empty_0121 x)

theorem nb077_wpp_notmem_0400 (F : Class) (I : Class) : (nb077_alpha_dummy_147 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_147, fv_syn_c0] using (nb077_compact_fv_empty_0122 F I)

theorem nb077_wpp_notmem_0401 (x : Var) : (nb077_alpha_dummy_149 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_149, fv_syn_c0] using (nb077_compact_fv_empty_0123 x)

theorem nb077_wpp_notmem_0402 (F : Class) (I : Class) : (nb077_alpha_dummy_153 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_153, fv_syn_c0] using (nb077_compact_fv_empty_0124 F I)

theorem nb077_wpp_notmem_0403 (x : Var) : (nb077_alpha_dummy_154 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_154, fv_syn_c0] using (nb077_compact_fv_empty_0125 x)

theorem nb077_wpp_notmem_0404 (F : Class) (I : Class) : (nb077_alpha_dummy_151 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_151, fv_syn_c0] using (nb077_compact_fv_empty_0126 F I)

theorem nb077_wpp_notmem_0405 (x : Var) : (nb077_alpha_dummy_152 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_152, fv_syn_c0] using (nb077_compact_fv_empty_0127 x)

theorem nb077_wpp_notmem_0406 (F : Class) (I : Class) : (nb077_alpha_dummy_140 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_140, fv_syn_c0] using (nb077_compact_fv_empty_0128 F I)

theorem nb077_wpp_notmem_0407 (x : Var) : (nb077_alpha_dummy_143 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_143, fv_syn_c0] using (nb077_compact_fv_empty_0129 x)

theorem nb077_wpp_notmem_0408 (F : Class) (I : Class) : (nb077_alpha_dummy_139 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_139, fv_syn_c0] using (nb077_compact_fv_empty_0130 F I)

theorem nb077_wpp_notmem_0409 (x : Var) : (nb077_alpha_dummy_142 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_142, fv_syn_c0] using (nb077_compact_fv_empty_0131 x)

theorem nb077_wpp_notmem_0410 (F : Class) (I : Class) : (nb077_alpha_dummy_145 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_145, fv_syn_c0] using (nb077_compact_fv_empty_0132 F I)

theorem nb077_wpp_notmem_0411 (x : Var) : (nb077_alpha_dummy_146 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_146, fv_syn_c0] using (nb077_compact_fv_empty_0133 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
