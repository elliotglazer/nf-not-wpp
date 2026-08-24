import NAR4C076C001Part009

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

noncomputable def nb076_split_alpha_0004 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) (dv_a_b : a ≠ b) (dv_a_g : a ≠ g) : TAlphaWff [((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_087)) (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))) (Wff.neg (Wff.classMem (Class.cv (nb076_alpha_dummy_087)) (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000)) (Wff.classEq (Class.cv (nb076_alpha_dummy_081)) (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))))) (Wff.imp (Wff.classMem (Class.cv (nb076_alpha_dummy_088 g a b)) (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))) (Wff.neg (Wff.classMem (Class.cv (nb076_alpha_dummy_088 g a b)) (Class.cab (nb076_alpha_dummy_083 g a b) (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a) (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b)) (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0097 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0093) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0095 g a b) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_g (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_b (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) (by decide)) (freshVar_injective (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0099 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0098) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0099 g a b) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_082))).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0102) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0103 g a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0103 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0101 g a b) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096), (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095), (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (nb076_wpp_refl_0015 g m n a b))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0107 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0105 g a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0111 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0109 g a b) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0107 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0105 g a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0111 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0109 g a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096), (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095), (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (nb076_wpp_refl_0016 g m n a b))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0115 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0113 g a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0115 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0113 g a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0119 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0117 g a b) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0119 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0117 g a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0101 g a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (nb076_wpp_refl_0017 g m n a b))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0101 g a b) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0101 g a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (nb076_wpp_refl_0017 g m n a b)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0097 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0093) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0095 g a b) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_g (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_b (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) (by decide)) (freshVar_injective (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0099 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0098) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0099 g a b) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_082))).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0102) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0103 g a b) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0103 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0101 g a b) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096), (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095), (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_c1c) (nb076_wpp_refl_0015 g m n a b))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0107 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0105 g a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0111 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0109 g a b) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0107 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0105 g a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0111 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0109 g a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_097), (nb076_alpha_dummy_100 g a b)), ((nb076_alpha_dummy_096), (nb076_alpha_dummy_099 g a b)), ((nb076_alpha_dummy_095), (nb076_alpha_dummy_098 g a b)), ((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_c0) (nb076_wpp_refl_0016 g m n a b))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0115 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0113 g a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0115 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0113 g a b) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0119 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0117 g a b) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0119 g a b) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0117 g a b) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0101 g a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (nb076_wpp_refl_0017 g m n a b))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0101 g a b) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0101 g a b) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb076_alpha_dummy_093), (nb076_alpha_dummy_094 g a b)), ((nb076_alpha_dummy_089), (nb076_alpha_dummy_091 g a b)), ((nb076_alpha_dummy_090), (nb076_alpha_dummy_092 g a b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_087), (nb076_alpha_dummy_088 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] (syn_cnnc) (nb076_wpp_refl_0017 g m n a b))))))))))))))))))))))))))))

theorem nb076_compact_fv_empty_0086 : (nb076_alpha_dummy_135) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0278 : (nb076_alpha_dummy_135) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_135, fv_syn_c1c] using (nb076_compact_fv_empty_0086)

theorem nb076_compact_fv_empty_0087 (g : Var) (b : Var) : (nb076_alpha_dummy_138 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0279 (g : Var) (b : Var) : (nb076_alpha_dummy_138 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_138, fv_syn_c1c] using (nb076_compact_fv_empty_0087 g b)

theorem nb076_compact_fv_empty_0088 : (nb076_alpha_dummy_134) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0280 : (nb076_alpha_dummy_134) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_134, fv_syn_c1c] using (nb076_compact_fv_empty_0088)

theorem nb076_compact_fv_empty_0089 (g : Var) (b : Var) : (nb076_alpha_dummy_137 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0281 (g : Var) (b : Var) : (nb076_alpha_dummy_137 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_137, fv_syn_c1c] using (nb076_compact_fv_empty_0089 g b)

theorem nb076_compact_fv_empty_0090 : (nb076_alpha_dummy_133) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0282 : (nb076_alpha_dummy_133) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_133, fv_syn_c1c] using (nb076_compact_fv_empty_0090)

theorem nb076_compact_fv_empty_0091 (g : Var) (b : Var) : (nb076_alpha_dummy_136 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0283 (g : Var) (b : Var) : (nb076_alpha_dummy_136 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_136, fv_syn_c1c] using (nb076_compact_fv_empty_0091 g b)

theorem nb076_compact_fv_empty_0092 : (nb076_alpha_dummy_131) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0284 : (nb076_alpha_dummy_131) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_131, fv_syn_c1c] using (nb076_compact_fv_empty_0092)

theorem nb076_compact_fv_empty_0093 (g : Var) (b : Var) : (nb076_alpha_dummy_132 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0285 (g : Var) (b : Var) : (nb076_alpha_dummy_132 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_132, fv_syn_c1c] using (nb076_compact_fv_empty_0093 g b)

theorem nb076_compact_fv_empty_0094 : (nb076_alpha_dummy_127) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0286 : (nb076_alpha_dummy_127) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_127, fv_syn_c1c] using (nb076_compact_fv_empty_0094)

theorem nb076_compact_fv_empty_0095 (g : Var) (b : Var) : (nb076_alpha_dummy_129 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0287 (g : Var) (b : Var) : (nb076_alpha_dummy_129 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_129, fv_syn_c1c] using (nb076_compact_fv_empty_0095 g b)

theorem nb076_compact_fv_empty_0096 : (nb076_alpha_dummy_128) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0288 : (nb076_alpha_dummy_128) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_128, fv_syn_c1c] using (nb076_compact_fv_empty_0096)

theorem nb076_compact_fv_empty_0097 (g : Var) (b : Var) : (nb076_alpha_dummy_130 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0289 (g : Var) (b : Var) : (nb076_alpha_dummy_130 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_130, fv_syn_c1c] using (nb076_compact_fv_empty_0097 g b)

theorem nb076_compact_fv_empty_0098 : (nb076_alpha_dummy_120) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0290 : (nb076_alpha_dummy_120) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_120, fv_syn_c1c] using (nb076_compact_fv_empty_0098)

theorem nb076_compact_fv_empty_0099 (g : Var) (b : Var) : (nb076_alpha_dummy_122 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0291 (g : Var) (b : Var) : (nb076_alpha_dummy_122 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_122, fv_syn_c1c] using (nb076_compact_fv_empty_0099 g b)

theorem nb076_compact_fv_empty_0100 : (nb076_alpha_dummy_119) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0292 : (nb076_alpha_dummy_119) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_119, fv_syn_c1c] using (nb076_compact_fv_empty_0100)

theorem nb076_compact_fv_empty_0101 (g : Var) (b : Var) : (nb076_alpha_dummy_121 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0293 (g : Var) (b : Var) : (nb076_alpha_dummy_121 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_121, fv_syn_c1c] using (nb076_compact_fv_empty_0101 g b)

theorem nb076_compact_fv_empty_0102 : (nb076_alpha_dummy_125) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0294 : (nb076_alpha_dummy_125) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_125, fv_syn_c1c] using (nb076_compact_fv_empty_0102)

theorem nb076_compact_fv_empty_0103 (g : Var) (b : Var) : (nb076_alpha_dummy_126 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0295 (g : Var) (b : Var) : (nb076_alpha_dummy_126 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_126, fv_syn_c1c] using (nb076_compact_fv_empty_0103 g b)

theorem nb076_compact_fv_empty_0104 : (nb076_alpha_dummy_123) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0296 : (nb076_alpha_dummy_123) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_123, fv_syn_c1c] using (nb076_compact_fv_empty_0104)

theorem nb076_compact_fv_empty_0105 (g : Var) (b : Var) : (nb076_alpha_dummy_124 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0297 (g : Var) (b : Var) : (nb076_alpha_dummy_124 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_124, fv_syn_c1c] using (nb076_compact_fv_empty_0105 g b)

theorem nb076_compact_fv_empty_0106 : (nb076_alpha_dummy_114) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0298 : (nb076_alpha_dummy_114) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_114, fv_syn_c1c] using (nb076_compact_fv_empty_0106)

theorem nb076_compact_fv_empty_0107 (g : Var) (b : Var) : (nb076_alpha_dummy_116 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0299 (g : Var) (b : Var) : (nb076_alpha_dummy_116 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_116, fv_syn_c1c] using (nb076_compact_fv_empty_0107 g b)

theorem nb076_compact_fv_empty_0108 : (nb076_alpha_dummy_113) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0300 : (nb076_alpha_dummy_113) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_113, fv_syn_c1c] using (nb076_compact_fv_empty_0108)

theorem nb076_compact_fv_empty_0109 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0301 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_115, fv_syn_c1c] using (nb076_compact_fv_empty_0109 g b)

theorem nb076_compact_fv_empty_0110 : (nb076_alpha_dummy_117) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0302 : (nb076_alpha_dummy_117) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_117, fv_syn_c1c] using (nb076_compact_fv_empty_0110)

theorem nb076_compact_fv_empty_0111 (g : Var) (b : Var) : (nb076_alpha_dummy_118 g b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0303 (g : Var) (b : Var) : (nb076_alpha_dummy_118 g b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_118, fv_syn_c1c] using (nb076_compact_fv_empty_0111 g b)

theorem nb076_compact_fv_empty_0112 : (nb076_alpha_dummy_111) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0304 : (nb076_alpha_dummy_111) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_111, fv_syn_c1c] using (nb076_compact_fv_empty_0112)

theorem nb076_compact_fv_empty_0113 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_112 g a b) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb076_wpp_notmem_0305 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_112 g a b) ∉ ((syn_c1c)).fv := by
  simpa only [nb076_alpha_dummy_112, fv_syn_c1c] using (nb076_compact_fv_empty_0113 g a b)

theorem nb076_compact_envfresh_0018 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TEnvFresh [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134), (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)), ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)), ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)), ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb076_alpha_dummy_135) (nb076_alpha_dummy_138 g b) (nb076_wpp_notmem_0278) (nb076_wpp_notmem_0279 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_134) (nb076_alpha_dummy_137 g b) (nb076_wpp_notmem_0280) (nb076_wpp_notmem_0281 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_133) (nb076_alpha_dummy_136 g b) (nb076_wpp_notmem_0282) (nb076_wpp_notmem_0283 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_131) (nb076_alpha_dummy_132 g b) (nb076_wpp_notmem_0284) (nb076_wpp_notmem_0285 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_127) (nb076_alpha_dummy_129 g b) (nb076_wpp_notmem_0286) (nb076_wpp_notmem_0287 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_128) (nb076_alpha_dummy_130 g b) (nb076_wpp_notmem_0288) (nb076_wpp_notmem_0289 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_120) (nb076_alpha_dummy_122 g b) (nb076_wpp_notmem_0290) (nb076_wpp_notmem_0291 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_119) (nb076_alpha_dummy_121 g b) (nb076_wpp_notmem_0292) (nb076_wpp_notmem_0293 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_125) (nb076_alpha_dummy_126 g b) (nb076_wpp_notmem_0294) (nb076_wpp_notmem_0295 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_123) (nb076_alpha_dummy_124 g b) (nb076_wpp_notmem_0296) (nb076_wpp_notmem_0297 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_114) (nb076_alpha_dummy_116 g b) (nb076_wpp_notmem_0298) (nb076_wpp_notmem_0299 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_113) (nb076_alpha_dummy_115 g b) (nb076_wpp_notmem_0300) (nb076_wpp_notmem_0301 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_117) (nb076_alpha_dummy_118 g b) (nb076_wpp_notmem_0302) (nb076_wpp_notmem_0303 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_082) (nb076_alpha_dummy_084 g a b) (nb076_wpp_notmem_0218) (nb076_wpp_notmem_0219 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_081) (nb076_alpha_dummy_083 g a b) (nb076_wpp_notmem_0220) (nb076_wpp_notmem_0221 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_111) (nb076_alpha_dummy_112 g a b) (nb076_wpp_notmem_0304) (nb076_wpp_notmem_0305 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_085) (nb076_alpha_dummy_086 g a b) (nb076_wpp_notmem_0224) (nb076_wpp_notmem_0225 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_002) g (nb076_wpp_notmem_0226) (nb076_wpp_notmem_0227 g) (TEnvFresh.consFresh (nb076_alpha_dummy_001) b (nb076_wpp_notmem_0228) (nb076_wpp_notmem_0229 b) (TEnvFresh.consFresh (nb076_alpha_dummy_000) a (nb076_wpp_notmem_0230) (nb076_wpp_notmem_0231 a) (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b) (nb076_wpp_notmem_0028) (nb076_wpp_notmem_0029 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0030) (nb076_wpp_notmem_0031 n) (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0032) (nb076_wpp_notmem_0033 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0034) (nb076_wpp_notmem_0035 g m n a b) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))))

noncomputable def nb076_wpp_refl_0018 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TReflOn [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134), (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)), ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)), ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)), ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0018 g m n a b)

theorem nb076_wpp_notmem_0306 : (nb076_alpha_dummy_135) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_135, fv_syn_c0] using (nb076_compact_fv_empty_0086)

theorem nb076_wpp_notmem_0307 (g : Var) (b : Var) : (nb076_alpha_dummy_138 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_138, fv_syn_c0] using (nb076_compact_fv_empty_0087 g b)

theorem nb076_wpp_notmem_0308 : (nb076_alpha_dummy_134) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_134, fv_syn_c0] using (nb076_compact_fv_empty_0088)

theorem nb076_wpp_notmem_0309 (g : Var) (b : Var) : (nb076_alpha_dummy_137 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_137, fv_syn_c0] using (nb076_compact_fv_empty_0089 g b)

theorem nb076_wpp_notmem_0310 : (nb076_alpha_dummy_133) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_133, fv_syn_c0] using (nb076_compact_fv_empty_0090)

theorem nb076_wpp_notmem_0311 (g : Var) (b : Var) : (nb076_alpha_dummy_136 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_136, fv_syn_c0] using (nb076_compact_fv_empty_0091 g b)

theorem nb076_wpp_notmem_0312 : (nb076_alpha_dummy_131) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_131, fv_syn_c0] using (nb076_compact_fv_empty_0092)

theorem nb076_wpp_notmem_0313 (g : Var) (b : Var) : (nb076_alpha_dummy_132 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_132, fv_syn_c0] using (nb076_compact_fv_empty_0093 g b)

theorem nb076_wpp_notmem_0314 : (nb076_alpha_dummy_127) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_127, fv_syn_c0] using (nb076_compact_fv_empty_0094)

theorem nb076_wpp_notmem_0315 (g : Var) (b : Var) : (nb076_alpha_dummy_129 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_129, fv_syn_c0] using (nb076_compact_fv_empty_0095 g b)

theorem nb076_wpp_notmem_0316 : (nb076_alpha_dummy_128) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_128, fv_syn_c0] using (nb076_compact_fv_empty_0096)

theorem nb076_wpp_notmem_0317 (g : Var) (b : Var) : (nb076_alpha_dummy_130 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_130, fv_syn_c0] using (nb076_compact_fv_empty_0097 g b)

theorem nb076_wpp_notmem_0318 : (nb076_alpha_dummy_120) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_120, fv_syn_c0] using (nb076_compact_fv_empty_0098)

theorem nb076_wpp_notmem_0319 (g : Var) (b : Var) : (nb076_alpha_dummy_122 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_122, fv_syn_c0] using (nb076_compact_fv_empty_0099 g b)

theorem nb076_wpp_notmem_0320 : (nb076_alpha_dummy_119) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_119, fv_syn_c0] using (nb076_compact_fv_empty_0100)

theorem nb076_wpp_notmem_0321 (g : Var) (b : Var) : (nb076_alpha_dummy_121 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_121, fv_syn_c0] using (nb076_compact_fv_empty_0101 g b)

theorem nb076_wpp_notmem_0322 : (nb076_alpha_dummy_125) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_125, fv_syn_c0] using (nb076_compact_fv_empty_0102)

theorem nb076_wpp_notmem_0323 (g : Var) (b : Var) : (nb076_alpha_dummy_126 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_126, fv_syn_c0] using (nb076_compact_fv_empty_0103 g b)

theorem nb076_wpp_notmem_0324 : (nb076_alpha_dummy_123) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_123, fv_syn_c0] using (nb076_compact_fv_empty_0104)

theorem nb076_wpp_notmem_0325 (g : Var) (b : Var) : (nb076_alpha_dummy_124 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_124, fv_syn_c0] using (nb076_compact_fv_empty_0105 g b)

theorem nb076_wpp_notmem_0326 : (nb076_alpha_dummy_114) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_114, fv_syn_c0] using (nb076_compact_fv_empty_0106)

theorem nb076_wpp_notmem_0327 (g : Var) (b : Var) : (nb076_alpha_dummy_116 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_116, fv_syn_c0] using (nb076_compact_fv_empty_0107 g b)

theorem nb076_wpp_notmem_0328 : (nb076_alpha_dummy_113) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_113, fv_syn_c0] using (nb076_compact_fv_empty_0108)

theorem nb076_wpp_notmem_0329 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_115, fv_syn_c0] using (nb076_compact_fv_empty_0109 g b)

theorem nb076_wpp_notmem_0330 : (nb076_alpha_dummy_117) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_117, fv_syn_c0] using (nb076_compact_fv_empty_0110)

theorem nb076_wpp_notmem_0331 (g : Var) (b : Var) : (nb076_alpha_dummy_118 g b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_118, fv_syn_c0] using (nb076_compact_fv_empty_0111 g b)

theorem nb076_wpp_notmem_0332 : (nb076_alpha_dummy_111) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_111, fv_syn_c0] using (nb076_compact_fv_empty_0112)

theorem nb076_wpp_notmem_0333 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_112 g a b) ∉ ((syn_c0)).fv := by
  simpa only [nb076_alpha_dummy_112, fv_syn_c0] using (nb076_compact_fv_empty_0113 g a b)

theorem nb076_compact_envfresh_0019 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TEnvFresh [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134), (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)), ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)), ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)), ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb076_alpha_dummy_135) (nb076_alpha_dummy_138 g b) (nb076_wpp_notmem_0306) (nb076_wpp_notmem_0307 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_134) (nb076_alpha_dummy_137 g b) (nb076_wpp_notmem_0308) (nb076_wpp_notmem_0309 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_133) (nb076_alpha_dummy_136 g b) (nb076_wpp_notmem_0310) (nb076_wpp_notmem_0311 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_131) (nb076_alpha_dummy_132 g b) (nb076_wpp_notmem_0312) (nb076_wpp_notmem_0313 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_127) (nb076_alpha_dummy_129 g b) (nb076_wpp_notmem_0314) (nb076_wpp_notmem_0315 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_128) (nb076_alpha_dummy_130 g b) (nb076_wpp_notmem_0316) (nb076_wpp_notmem_0317 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_120) (nb076_alpha_dummy_122 g b) (nb076_wpp_notmem_0318) (nb076_wpp_notmem_0319 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_119) (nb076_alpha_dummy_121 g b) (nb076_wpp_notmem_0320) (nb076_wpp_notmem_0321 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_125) (nb076_alpha_dummy_126 g b) (nb076_wpp_notmem_0322) (nb076_wpp_notmem_0323 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_123) (nb076_alpha_dummy_124 g b) (nb076_wpp_notmem_0324) (nb076_wpp_notmem_0325 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_114) (nb076_alpha_dummy_116 g b) (nb076_wpp_notmem_0326) (nb076_wpp_notmem_0327 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_113) (nb076_alpha_dummy_115 g b) (nb076_wpp_notmem_0328) (nb076_wpp_notmem_0329 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_117) (nb076_alpha_dummy_118 g b) (nb076_wpp_notmem_0330) (nb076_wpp_notmem_0331 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_082) (nb076_alpha_dummy_084 g a b) (nb076_wpp_notmem_0244) (nb076_wpp_notmem_0245 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_081) (nb076_alpha_dummy_083 g a b) (nb076_wpp_notmem_0246) (nb076_wpp_notmem_0247 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_111) (nb076_alpha_dummy_112 g a b) (nb076_wpp_notmem_0332) (nb076_wpp_notmem_0333 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_085) (nb076_alpha_dummy_086 g a b) (nb076_wpp_notmem_0250) (nb076_wpp_notmem_0251 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_002) g (nb076_wpp_notmem_0252) (nb076_wpp_notmem_0253 g) (TEnvFresh.consFresh (nb076_alpha_dummy_001) b (nb076_wpp_notmem_0254) (nb076_wpp_notmem_0255 b) (TEnvFresh.consFresh (nb076_alpha_dummy_000) a (nb076_wpp_notmem_0256) (nb076_wpp_notmem_0257 a) (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b) (nb076_wpp_notmem_0064) (nb076_wpp_notmem_0065 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0066) (nb076_wpp_notmem_0067 n) (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0068) (nb076_wpp_notmem_0069 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0070) (nb076_wpp_notmem_0071 g m n a b) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))))

noncomputable def nb076_wpp_refl_0019 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TReflOn [((nb076_alpha_dummy_135), (nb076_alpha_dummy_138 g b)), ((nb076_alpha_dummy_134), (nb076_alpha_dummy_137 g b)), ((nb076_alpha_dummy_133), (nb076_alpha_dummy_136 g b)), ((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)), ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)), ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0019 g m n a b)

theorem nb076_wpp_notmem_0334 : (nb076_alpha_dummy_131) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_131, fv_syn_cnnc] using (nb076_compact_fv_empty_0092)

theorem nb076_wpp_notmem_0335 (g : Var) (b : Var) : (nb076_alpha_dummy_132 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_132, fv_syn_cnnc] using (nb076_compact_fv_empty_0093 g b)

theorem nb076_wpp_notmem_0336 : (nb076_alpha_dummy_127) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_127, fv_syn_cnnc] using (nb076_compact_fv_empty_0094)

theorem nb076_wpp_notmem_0337 (g : Var) (b : Var) : (nb076_alpha_dummy_129 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_129, fv_syn_cnnc] using (nb076_compact_fv_empty_0095 g b)

theorem nb076_wpp_notmem_0338 : (nb076_alpha_dummy_128) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_128, fv_syn_cnnc] using (nb076_compact_fv_empty_0096)

theorem nb076_wpp_notmem_0339 (g : Var) (b : Var) : (nb076_alpha_dummy_130 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_130, fv_syn_cnnc] using (nb076_compact_fv_empty_0097 g b)

theorem nb076_wpp_notmem_0340 : (nb076_alpha_dummy_120) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_120, fv_syn_cnnc] using (nb076_compact_fv_empty_0098)

theorem nb076_wpp_notmem_0341 (g : Var) (b : Var) : (nb076_alpha_dummy_122 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_122, fv_syn_cnnc] using (nb076_compact_fv_empty_0099 g b)

theorem nb076_wpp_notmem_0342 : (nb076_alpha_dummy_119) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_119, fv_syn_cnnc] using (nb076_compact_fv_empty_0100)

theorem nb076_wpp_notmem_0343 (g : Var) (b : Var) : (nb076_alpha_dummy_121 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_121, fv_syn_cnnc] using (nb076_compact_fv_empty_0101 g b)

theorem nb076_wpp_notmem_0344 : (nb076_alpha_dummy_125) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_125, fv_syn_cnnc] using (nb076_compact_fv_empty_0102)

theorem nb076_wpp_notmem_0345 (g : Var) (b : Var) : (nb076_alpha_dummy_126 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_126, fv_syn_cnnc] using (nb076_compact_fv_empty_0103 g b)

theorem nb076_wpp_notmem_0346 : (nb076_alpha_dummy_123) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_123, fv_syn_cnnc] using (nb076_compact_fv_empty_0104)

theorem nb076_wpp_notmem_0347 (g : Var) (b : Var) : (nb076_alpha_dummy_124 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_124, fv_syn_cnnc] using (nb076_compact_fv_empty_0105 g b)

theorem nb076_wpp_notmem_0348 : (nb076_alpha_dummy_114) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_114, fv_syn_cnnc] using (nb076_compact_fv_empty_0106)

theorem nb076_wpp_notmem_0349 (g : Var) (b : Var) : (nb076_alpha_dummy_116 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_116, fv_syn_cnnc] using (nb076_compact_fv_empty_0107 g b)

theorem nb076_wpp_notmem_0350 : (nb076_alpha_dummy_113) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_113, fv_syn_cnnc] using (nb076_compact_fv_empty_0108)

theorem nb076_wpp_notmem_0351 (g : Var) (b : Var) : (nb076_alpha_dummy_115 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_115, fv_syn_cnnc] using (nb076_compact_fv_empty_0109 g b)

theorem nb076_wpp_notmem_0352 : (nb076_alpha_dummy_117) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_117, fv_syn_cnnc] using (nb076_compact_fv_empty_0110)

theorem nb076_wpp_notmem_0353 (g : Var) (b : Var) : (nb076_alpha_dummy_118 g b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_118, fv_syn_cnnc] using (nb076_compact_fv_empty_0111 g b)

theorem nb076_wpp_notmem_0354 : (nb076_alpha_dummy_111) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_111, fv_syn_cnnc] using (nb076_compact_fv_empty_0112)

theorem nb076_wpp_notmem_0355 (g : Var) (a : Var) (b : Var) : (nb076_alpha_dummy_112 g a b) ∉ ((syn_cnnc)).fv := by
  simpa only [nb076_alpha_dummy_112, fv_syn_cnnc] using (nb076_compact_fv_empty_0113 g a b)

theorem nb076_compact_envfresh_0020 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) : TEnvFresh [((nb076_alpha_dummy_131), (nb076_alpha_dummy_132 g b)), ((nb076_alpha_dummy_127), (nb076_alpha_dummy_129 g b)), ((nb076_alpha_dummy_128), (nb076_alpha_dummy_130 g b)), ((nb076_alpha_dummy_120), (nb076_alpha_dummy_122 g b)), ((nb076_alpha_dummy_119), (nb076_alpha_dummy_121 g b)), ((nb076_alpha_dummy_125), (nb076_alpha_dummy_126 g b)), ((nb076_alpha_dummy_123), (nb076_alpha_dummy_124 g b)), ((nb076_alpha_dummy_114), (nb076_alpha_dummy_116 g b)), ((nb076_alpha_dummy_113), (nb076_alpha_dummy_115 g b)), ((nb076_alpha_dummy_117), (nb076_alpha_dummy_118 g b)), ((nb076_alpha_dummy_082), (nb076_alpha_dummy_084 g a b)), ((nb076_alpha_dummy_081), (nb076_alpha_dummy_083 g a b)), ((nb076_alpha_dummy_111), (nb076_alpha_dummy_112 g a b)), ((nb076_alpha_dummy_085), (nb076_alpha_dummy_086 g a b)), ((nb076_alpha_dummy_002), g), ((nb076_alpha_dummy_001), b), ((nb076_alpha_dummy_000), a), ((nb076_alpha_dummy_005), (nb076_alpha_dummy_006 g m n a b)), ((nb076_alpha_dummy_004), n), ((nb076_alpha_dummy_003), m), ((nb076_alpha_dummy_007), (nb076_alpha_dummy_008 g m n a b))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb076_alpha_dummy_131) (nb076_alpha_dummy_132 g b) (nb076_wpp_notmem_0334) (nb076_wpp_notmem_0335 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_127) (nb076_alpha_dummy_129 g b) (nb076_wpp_notmem_0336) (nb076_wpp_notmem_0337 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_128) (nb076_alpha_dummy_130 g b) (nb076_wpp_notmem_0338) (nb076_wpp_notmem_0339 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_120) (nb076_alpha_dummy_122 g b) (nb076_wpp_notmem_0340) (nb076_wpp_notmem_0341 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_119) (nb076_alpha_dummy_121 g b) (nb076_wpp_notmem_0342) (nb076_wpp_notmem_0343 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_125) (nb076_alpha_dummy_126 g b) (nb076_wpp_notmem_0344) (nb076_wpp_notmem_0345 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_123) (nb076_alpha_dummy_124 g b) (nb076_wpp_notmem_0346) (nb076_wpp_notmem_0347 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_114) (nb076_alpha_dummy_116 g b) (nb076_wpp_notmem_0348) (nb076_wpp_notmem_0349 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_113) (nb076_alpha_dummy_115 g b) (nb076_wpp_notmem_0350) (nb076_wpp_notmem_0351 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_117) (nb076_alpha_dummy_118 g b) (nb076_wpp_notmem_0352) (nb076_wpp_notmem_0353 g b) (TEnvFresh.consFresh (nb076_alpha_dummy_082) (nb076_alpha_dummy_084 g a b) (nb076_wpp_notmem_0264) (nb076_wpp_notmem_0265 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_081) (nb076_alpha_dummy_083 g a b) (nb076_wpp_notmem_0266) (nb076_wpp_notmem_0267 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_111) (nb076_alpha_dummy_112 g a b) (nb076_wpp_notmem_0354) (nb076_wpp_notmem_0355 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_085) (nb076_alpha_dummy_086 g a b) (nb076_wpp_notmem_0270) (nb076_wpp_notmem_0271 g a b) (TEnvFresh.consFresh (nb076_alpha_dummy_002) g (nb076_wpp_notmem_0272) (nb076_wpp_notmem_0273 g) (TEnvFresh.consFresh (nb076_alpha_dummy_001) b (nb076_wpp_notmem_0274) (nb076_wpp_notmem_0275 b) (TEnvFresh.consFresh (nb076_alpha_dummy_000) a (nb076_wpp_notmem_0276) (nb076_wpp_notmem_0277 a) (TEnvFresh.consFresh (nb076_alpha_dummy_005) (nb076_alpha_dummy_006 g m n a b) (nb076_wpp_notmem_0094) (nb076_wpp_notmem_0095 g m n a b) (TEnvFresh.consFresh (nb076_alpha_dummy_004) n (nb076_wpp_notmem_0096) (nb076_wpp_notmem_0097 n) (TEnvFresh.consFresh (nb076_alpha_dummy_003) m (nb076_wpp_notmem_0098) (nb076_wpp_notmem_0099 m) (TEnvFresh.consFresh (nb076_alpha_dummy_007) (nb076_alpha_dummy_008 g m n a b) (nb076_wpp_notmem_0100) (nb076_wpp_notmem_0101 g m n a b) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
