import NAR4C078C001Part131

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

noncomputable def nb078_split_alpha_0109 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_923)) (syn_cphi (Class.cv (nb078_alpha_dummy_890)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_923)) (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_924 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_924 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0927 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0927 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0956) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0957 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0954) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0955 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_892 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0930) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0931 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0930) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0931 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0928) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0929 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0361 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0934) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0935 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0932) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0933 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0938) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0939 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0936) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0937 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0934) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0935 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0932) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0933 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0938) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0939 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0936) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0937 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0362 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0942) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0943 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0940) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0941 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0942) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0943 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0940) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0941 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0946) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0947 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0944) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0945 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0946) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0947 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0944) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0945 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0928) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0929 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0363 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0928) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0929 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0928) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0929 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0363 x y h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0927 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0926) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0927 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0956) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0957 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0954) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0955 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_890))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_892 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0930) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0931 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0930) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0931 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0928) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0929 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0361 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0934) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0935 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0932) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0933 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0938) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0939 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0936) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0937 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0934) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0935 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0932) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0933 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0938) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0939 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0936) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0937 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0362 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0942) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0943 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0940) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0941 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0942) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0943 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0940) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0941 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0946) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0947 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0944) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0945 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0946) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0947 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0944) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0945 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0928) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0929 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0363 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0928) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0929 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0928) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0929 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_923), (nb078_alpha_dummy_924 h)), ((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0363 x y h))))))))))))))))))))

theorem nb078_wpp_notmem_2332 : (nb078_alpha_dummy_921) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_921, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0696)

theorem nb078_wpp_notmem_2333 (h : Var) : (nb078_alpha_dummy_922 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_922, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0697 h)

theorem nb078_wpp_notmem_2334 : (nb078_alpha_dummy_890) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_890, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0686)

theorem nb078_wpp_notmem_2335 (h : Var) : (nb078_alpha_dummy_892 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_892, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0687 h)

theorem nb078_wpp_notmem_2336 : (nb078_alpha_dummy_889) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_889, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0688)

theorem nb078_wpp_notmem_2337 (h : Var) : (nb078_alpha_dummy_891 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_891, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0689 h)

theorem nb078_wpp_notmem_2338 : (nb078_alpha_dummy_919) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_919, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0698)

theorem nb078_wpp_notmem_2339 (h : Var) : (nb078_alpha_dummy_920 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_920, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0699 h)

theorem nb078_wpp_notmem_2340 : (nb078_alpha_dummy_893) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_893, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0692)

theorem nb078_wpp_notmem_2341 (h : Var) : (nb078_alpha_dummy_894 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_894, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0693 h)

theorem nb078_compact_envfresh_0364 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_921) (nb078_alpha_dummy_922 h) (nb078_wpp_notmem_2332) (nb078_wpp_notmem_2333 h) (TEnvFresh.consFresh (nb078_alpha_dummy_890) (nb078_alpha_dummy_892 h) (nb078_wpp_notmem_2334) (nb078_wpp_notmem_2335 h) (TEnvFresh.consFresh (nb078_alpha_dummy_889) (nb078_alpha_dummy_891 h) (nb078_wpp_notmem_2336) (nb078_wpp_notmem_2337 h) (TEnvFresh.consFresh (nb078_alpha_dummy_919) (nb078_alpha_dummy_920 h) (nb078_wpp_notmem_2338) (nb078_wpp_notmem_2339 h) (TEnvFresh.consFresh (nb078_alpha_dummy_893) (nb078_alpha_dummy_894 h) (nb078_wpp_notmem_2340) (nb078_wpp_notmem_2341 h) (TEnvFresh.consFresh (nb078_alpha_dummy_848) (nb078_alpha_dummy_850 h) (nb078_wpp_notmem_2254) (nb078_wpp_notmem_2255 h) (TEnvFresh.consFresh (nb078_alpha_dummy_847) (nb078_alpha_dummy_849 h) (nb078_wpp_notmem_2256) (nb078_wpp_notmem_2257 h) (TEnvFresh.consFresh (nb078_alpha_dummy_851) (nb078_alpha_dummy_852 h) (nb078_wpp_notmem_2258) (nb078_wpp_notmem_2259 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2152) (nb078_wpp_notmem_2153 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_2052) (nb078_wpp_notmem_2053 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_2054) (nb078_wpp_notmem_2055 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_2056) (nb078_wpp_notmem_2057 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_2058) (nb078_wpp_notmem_2059 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_2060) (nb078_wpp_notmem_2061 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2062) (nb078_wpp_notmem_2063 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0364 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_921), (nb078_alpha_dummy_922 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_919), (nb078_alpha_dummy_920 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0364 x y h)

theorem nb078_compact_fv_empty_0700 : (nb078_alpha_dummy_941) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2342 : (nb078_alpha_dummy_941) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_941, fv_syn_c1c] using (nb078_compact_fv_empty_0700)

theorem nb078_compact_fv_empty_0701 (h : Var) : (nb078_alpha_dummy_944 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2343 (h : Var) : (nb078_alpha_dummy_944 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_944, fv_syn_c1c] using (nb078_compact_fv_empty_0701 h)

theorem nb078_compact_fv_empty_0702 : (nb078_alpha_dummy_940) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2344 : (nb078_alpha_dummy_940) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_940, fv_syn_c1c] using (nb078_compact_fv_empty_0702)

theorem nb078_compact_fv_empty_0703 (h : Var) : (nb078_alpha_dummy_943 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2345 (h : Var) : (nb078_alpha_dummy_943 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_943, fv_syn_c1c] using (nb078_compact_fv_empty_0703 h)

theorem nb078_compact_fv_empty_0704 : (nb078_alpha_dummy_939) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2346 : (nb078_alpha_dummy_939) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_939, fv_syn_c1c] using (nb078_compact_fv_empty_0704)

theorem nb078_compact_fv_empty_0705 (h : Var) : (nb078_alpha_dummy_942 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2347 (h : Var) : (nb078_alpha_dummy_942 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_942, fv_syn_c1c] using (nb078_compact_fv_empty_0705 h)

theorem nb078_compact_fv_empty_0706 : (nb078_alpha_dummy_937) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2348 : (nb078_alpha_dummy_937) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_937, fv_syn_c1c] using (nb078_compact_fv_empty_0706)

theorem nb078_compact_fv_empty_0707 (h : Var) : (nb078_alpha_dummy_938 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2349 (h : Var) : (nb078_alpha_dummy_938 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_938, fv_syn_c1c] using (nb078_compact_fv_empty_0707 h)

theorem nb078_compact_fv_empty_0708 : (nb078_alpha_dummy_933) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2350 : (nb078_alpha_dummy_933) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_933, fv_syn_c1c] using (nb078_compact_fv_empty_0708)

theorem nb078_compact_fv_empty_0709 (h : Var) : (nb078_alpha_dummy_935 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2351 (h : Var) : (nb078_alpha_dummy_935 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_935, fv_syn_c1c] using (nb078_compact_fv_empty_0709 h)

theorem nb078_compact_fv_empty_0710 : (nb078_alpha_dummy_934) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2352 : (nb078_alpha_dummy_934) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_934, fv_syn_c1c] using (nb078_compact_fv_empty_0710)

theorem nb078_compact_fv_empty_0711 (h : Var) : (nb078_alpha_dummy_936 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2353 (h : Var) : (nb078_alpha_dummy_936 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_936, fv_syn_c1c] using (nb078_compact_fv_empty_0711 h)

theorem nb078_compact_fv_empty_0712 : (nb078_alpha_dummy_926) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2354 : (nb078_alpha_dummy_926) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_926, fv_syn_c1c] using (nb078_compact_fv_empty_0712)

theorem nb078_compact_fv_empty_0713 (h : Var) : (nb078_alpha_dummy_928 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2355 (h : Var) : (nb078_alpha_dummy_928 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_928, fv_syn_c1c] using (nb078_compact_fv_empty_0713 h)

theorem nb078_compact_fv_empty_0714 : (nb078_alpha_dummy_925) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2356 : (nb078_alpha_dummy_925) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_925, fv_syn_c1c] using (nb078_compact_fv_empty_0714)

theorem nb078_compact_fv_empty_0715 (h : Var) : (nb078_alpha_dummy_927 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2357 (h : Var) : (nb078_alpha_dummy_927 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_927, fv_syn_c1c] using (nb078_compact_fv_empty_0715 h)

theorem nb078_compact_fv_empty_0716 : (nb078_alpha_dummy_931) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2358 : (nb078_alpha_dummy_931) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_931, fv_syn_c1c] using (nb078_compact_fv_empty_0716)

theorem nb078_compact_fv_empty_0717 (h : Var) : (nb078_alpha_dummy_932 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2359 (h : Var) : (nb078_alpha_dummy_932 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_932, fv_syn_c1c] using (nb078_compact_fv_empty_0717 h)

theorem nb078_compact_fv_empty_0718 : (nb078_alpha_dummy_929) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2360 : (nb078_alpha_dummy_929) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_929, fv_syn_c1c] using (nb078_compact_fv_empty_0718)

theorem nb078_compact_fv_empty_0719 (h : Var) : (nb078_alpha_dummy_930 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2361 (h : Var) : (nb078_alpha_dummy_930 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_930, fv_syn_c1c] using (nb078_compact_fv_empty_0719 h)

theorem nb078_compact_envfresh_0365 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940), (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)), ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_941) (nb078_alpha_dummy_944 h) (nb078_wpp_notmem_2342) (nb078_wpp_notmem_2343 h) (TEnvFresh.consFresh (nb078_alpha_dummy_940) (nb078_alpha_dummy_943 h) (nb078_wpp_notmem_2344) (nb078_wpp_notmem_2345 h) (TEnvFresh.consFresh (nb078_alpha_dummy_939) (nb078_alpha_dummy_942 h) (nb078_wpp_notmem_2346) (nb078_wpp_notmem_2347 h) (TEnvFresh.consFresh (nb078_alpha_dummy_937) (nb078_alpha_dummy_938 h) (nb078_wpp_notmem_2348) (nb078_wpp_notmem_2349 h) (TEnvFresh.consFresh (nb078_alpha_dummy_933) (nb078_alpha_dummy_935 h) (nb078_wpp_notmem_2350) (nb078_wpp_notmem_2351 h) (TEnvFresh.consFresh (nb078_alpha_dummy_934) (nb078_alpha_dummy_936 h) (nb078_wpp_notmem_2352) (nb078_wpp_notmem_2353 h) (TEnvFresh.consFresh (nb078_alpha_dummy_926) (nb078_alpha_dummy_928 h) (nb078_wpp_notmem_2354) (nb078_wpp_notmem_2355 h) (TEnvFresh.consFresh (nb078_alpha_dummy_925) (nb078_alpha_dummy_927 h) (nb078_wpp_notmem_2356) (nb078_wpp_notmem_2357 h) (TEnvFresh.consFresh (nb078_alpha_dummy_931) (nb078_alpha_dummy_932 h) (nb078_wpp_notmem_2358) (nb078_wpp_notmem_2359 h) (TEnvFresh.consFresh (nb078_alpha_dummy_929) (nb078_alpha_dummy_930 h) (nb078_wpp_notmem_2360) (nb078_wpp_notmem_2361 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2084) (nb078_wpp_notmem_2085 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1954) (nb078_wpp_notmem_1955 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1956) (nb078_wpp_notmem_1957 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1958) (nb078_wpp_notmem_1959 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1960) (nb078_wpp_notmem_1961 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1962) (nb078_wpp_notmem_1963 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0365 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940), (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)), ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0365 x y h)

theorem nb078_wpp_notmem_2362 : (nb078_alpha_dummy_941) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_941, fv_syn_c0] using (nb078_compact_fv_empty_0700)

theorem nb078_wpp_notmem_2363 (h : Var) : (nb078_alpha_dummy_944 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_944, fv_syn_c0] using (nb078_compact_fv_empty_0701 h)

theorem nb078_wpp_notmem_2364 : (nb078_alpha_dummy_940) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_940, fv_syn_c0] using (nb078_compact_fv_empty_0702)

theorem nb078_wpp_notmem_2365 (h : Var) : (nb078_alpha_dummy_943 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_943, fv_syn_c0] using (nb078_compact_fv_empty_0703 h)

theorem nb078_wpp_notmem_2366 : (nb078_alpha_dummy_939) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_939, fv_syn_c0] using (nb078_compact_fv_empty_0704)

theorem nb078_wpp_notmem_2367 (h : Var) : (nb078_alpha_dummy_942 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_942, fv_syn_c0] using (nb078_compact_fv_empty_0705 h)

theorem nb078_wpp_notmem_2368 : (nb078_alpha_dummy_937) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_937, fv_syn_c0] using (nb078_compact_fv_empty_0706)

theorem nb078_wpp_notmem_2369 (h : Var) : (nb078_alpha_dummy_938 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_938, fv_syn_c0] using (nb078_compact_fv_empty_0707 h)

theorem nb078_wpp_notmem_2370 : (nb078_alpha_dummy_933) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_933, fv_syn_c0] using (nb078_compact_fv_empty_0708)

theorem nb078_wpp_notmem_2371 (h : Var) : (nb078_alpha_dummy_935 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_935, fv_syn_c0] using (nb078_compact_fv_empty_0709 h)

theorem nb078_wpp_notmem_2372 : (nb078_alpha_dummy_934) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_934, fv_syn_c0] using (nb078_compact_fv_empty_0710)

theorem nb078_wpp_notmem_2373 (h : Var) : (nb078_alpha_dummy_936 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_936, fv_syn_c0] using (nb078_compact_fv_empty_0711 h)

theorem nb078_wpp_notmem_2374 : (nb078_alpha_dummy_926) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_926, fv_syn_c0] using (nb078_compact_fv_empty_0712)

theorem nb078_wpp_notmem_2375 (h : Var) : (nb078_alpha_dummy_928 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_928, fv_syn_c0] using (nb078_compact_fv_empty_0713 h)

theorem nb078_wpp_notmem_2376 : (nb078_alpha_dummy_925) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_925, fv_syn_c0] using (nb078_compact_fv_empty_0714)

theorem nb078_wpp_notmem_2377 (h : Var) : (nb078_alpha_dummy_927 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_927, fv_syn_c0] using (nb078_compact_fv_empty_0715 h)

theorem nb078_wpp_notmem_2378 : (nb078_alpha_dummy_931) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_931, fv_syn_c0] using (nb078_compact_fv_empty_0716)

theorem nb078_wpp_notmem_2379 (h : Var) : (nb078_alpha_dummy_932 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_932, fv_syn_c0] using (nb078_compact_fv_empty_0717 h)

theorem nb078_wpp_notmem_2380 : (nb078_alpha_dummy_929) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_929, fv_syn_c0] using (nb078_compact_fv_empty_0718)

theorem nb078_wpp_notmem_2381 (h : Var) : (nb078_alpha_dummy_930 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_930, fv_syn_c0] using (nb078_compact_fv_empty_0719 h)

theorem nb078_compact_envfresh_0366 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940), (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)), ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_941) (nb078_alpha_dummy_944 h) (nb078_wpp_notmem_2362) (nb078_wpp_notmem_2363 h) (TEnvFresh.consFresh (nb078_alpha_dummy_940) (nb078_alpha_dummy_943 h) (nb078_wpp_notmem_2364) (nb078_wpp_notmem_2365 h) (TEnvFresh.consFresh (nb078_alpha_dummy_939) (nb078_alpha_dummy_942 h) (nb078_wpp_notmem_2366) (nb078_wpp_notmem_2367 h) (TEnvFresh.consFresh (nb078_alpha_dummy_937) (nb078_alpha_dummy_938 h) (nb078_wpp_notmem_2368) (nb078_wpp_notmem_2369 h) (TEnvFresh.consFresh (nb078_alpha_dummy_933) (nb078_alpha_dummy_935 h) (nb078_wpp_notmem_2370) (nb078_wpp_notmem_2371 h) (TEnvFresh.consFresh (nb078_alpha_dummy_934) (nb078_alpha_dummy_936 h) (nb078_wpp_notmem_2372) (nb078_wpp_notmem_2373 h) (TEnvFresh.consFresh (nb078_alpha_dummy_926) (nb078_alpha_dummy_928 h) (nb078_wpp_notmem_2374) (nb078_wpp_notmem_2375 h) (TEnvFresh.consFresh (nb078_alpha_dummy_925) (nb078_alpha_dummy_927 h) (nb078_wpp_notmem_2376) (nb078_wpp_notmem_2377 h) (TEnvFresh.consFresh (nb078_alpha_dummy_931) (nb078_alpha_dummy_932 h) (nb078_wpp_notmem_2378) (nb078_wpp_notmem_2379 h) (TEnvFresh.consFresh (nb078_alpha_dummy_929) (nb078_alpha_dummy_930 h) (nb078_wpp_notmem_2380) (nb078_wpp_notmem_2381 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2106) (nb078_wpp_notmem_2107 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1986) (nb078_wpp_notmem_1987 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1988) (nb078_wpp_notmem_1989 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1990) (nb078_wpp_notmem_1991 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1992) (nb078_wpp_notmem_1993 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1994) (nb078_wpp_notmem_1995 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0366 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940), (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)), ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0366 x y h)

theorem nb078_wpp_notmem_2382 : (nb078_alpha_dummy_937) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_937, fv_syn_cnnc] using (nb078_compact_fv_empty_0706)

theorem nb078_wpp_notmem_2383 (h : Var) : (nb078_alpha_dummy_938 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_938, fv_syn_cnnc] using (nb078_compact_fv_empty_0707 h)

theorem nb078_wpp_notmem_2384 : (nb078_alpha_dummy_933) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_933, fv_syn_cnnc] using (nb078_compact_fv_empty_0708)

theorem nb078_wpp_notmem_2385 (h : Var) : (nb078_alpha_dummy_935 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_935, fv_syn_cnnc] using (nb078_compact_fv_empty_0709 h)

theorem nb078_wpp_notmem_2386 : (nb078_alpha_dummy_934) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_934, fv_syn_cnnc] using (nb078_compact_fv_empty_0710)

theorem nb078_wpp_notmem_2387 (h : Var) : (nb078_alpha_dummy_936 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_936, fv_syn_cnnc] using (nb078_compact_fv_empty_0711 h)

theorem nb078_wpp_notmem_2388 : (nb078_alpha_dummy_926) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_926, fv_syn_cnnc] using (nb078_compact_fv_empty_0712)

theorem nb078_wpp_notmem_2389 (h : Var) : (nb078_alpha_dummy_928 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_928, fv_syn_cnnc] using (nb078_compact_fv_empty_0713 h)

theorem nb078_wpp_notmem_2390 : (nb078_alpha_dummy_925) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_925, fv_syn_cnnc] using (nb078_compact_fv_empty_0714)

theorem nb078_wpp_notmem_2391 (h : Var) : (nb078_alpha_dummy_927 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_927, fv_syn_cnnc] using (nb078_compact_fv_empty_0715 h)

theorem nb078_wpp_notmem_2392 : (nb078_alpha_dummy_931) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_931, fv_syn_cnnc] using (nb078_compact_fv_empty_0716)

theorem nb078_wpp_notmem_2393 (h : Var) : (nb078_alpha_dummy_932 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_932, fv_syn_cnnc] using (nb078_compact_fv_empty_0717 h)

theorem nb078_wpp_notmem_2394 : (nb078_alpha_dummy_929) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_929, fv_syn_cnnc] using (nb078_compact_fv_empty_0718)

theorem nb078_wpp_notmem_2395 (h : Var) : (nb078_alpha_dummy_930 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_930, fv_syn_cnnc] using (nb078_compact_fv_empty_0719 h)

theorem nb078_compact_envfresh_0367 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_937) (nb078_alpha_dummy_938 h) (nb078_wpp_notmem_2382) (nb078_wpp_notmem_2383 h) (TEnvFresh.consFresh (nb078_alpha_dummy_933) (nb078_alpha_dummy_935 h) (nb078_wpp_notmem_2384) (nb078_wpp_notmem_2385 h) (TEnvFresh.consFresh (nb078_alpha_dummy_934) (nb078_alpha_dummy_936 h) (nb078_wpp_notmem_2386) (nb078_wpp_notmem_2387 h) (TEnvFresh.consFresh (nb078_alpha_dummy_926) (nb078_alpha_dummy_928 h) (nb078_wpp_notmem_2388) (nb078_wpp_notmem_2389 h) (TEnvFresh.consFresh (nb078_alpha_dummy_925) (nb078_alpha_dummy_927 h) (nb078_wpp_notmem_2390) (nb078_wpp_notmem_2391 h) (TEnvFresh.consFresh (nb078_alpha_dummy_931) (nb078_alpha_dummy_932 h) (nb078_wpp_notmem_2392) (nb078_wpp_notmem_2393 h) (TEnvFresh.consFresh (nb078_alpha_dummy_929) (nb078_alpha_dummy_930 h) (nb078_wpp_notmem_2394) (nb078_wpp_notmem_2395 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2122) (nb078_wpp_notmem_2123 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_2012) (nb078_wpp_notmem_2013 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_2014) (nb078_wpp_notmem_2015 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_2016) (nb078_wpp_notmem_2017 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_2018) (nb078_wpp_notmem_2019 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_2020) (nb078_wpp_notmem_2021 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb078_wpp_refl_0367 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_931), (nb078_alpha_dummy_932 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0367 x y h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
