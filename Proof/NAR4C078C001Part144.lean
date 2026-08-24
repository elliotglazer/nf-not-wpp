import NAR4C078C001Part143

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

noncomputable def nb078_split_alpha_0122 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_957)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_957)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_958 h)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_958 h)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0976) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0977 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0976) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0977 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1006) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1007 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1005 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_926))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_928 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0980) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0981 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0980) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0981 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0978) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0979 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940), (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)), ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0404 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0984) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0985 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0982) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0983 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0988) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0989 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0986) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0987 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0984) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0985 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0982) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0983 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0988) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0989 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0986) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0987 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940), (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)), ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0405 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0992) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0993 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0990) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0991 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0992) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0993 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0990) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0991 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0996) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0997 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0994) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0995 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0996) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0997 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0994) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0995 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0978) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0979 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0406 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0978) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0979 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0978) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0979 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0406 x y h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0976) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0977 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0976) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0977 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1006) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1007 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1004) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1005 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_926))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_928 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0980) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0981 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0980) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0981 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0978) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0979 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940), (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)), ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0404 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0984) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0985 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0982) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0983 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0988) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0989 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0986) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0987 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0984) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0985 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0982) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0983 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0988) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0989 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0986) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0987 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_941), (nb078_alpha_dummy_944 h)), ((nb078_alpha_dummy_940), (nb078_alpha_dummy_943 h)), ((nb078_alpha_dummy_939), (nb078_alpha_dummy_942 h)), ((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0405 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0992) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0993 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0990) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0991 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0992) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0993 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0990) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0991 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0996) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0997 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0994) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0995 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0996) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0997 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0994) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0995 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0978) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0979 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0406 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0978) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0979 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0978) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0979 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_937), (nb078_alpha_dummy_938 h)), ((nb078_alpha_dummy_933), (nb078_alpha_dummy_935 h)), ((nb078_alpha_dummy_934), (nb078_alpha_dummy_936 h)), ((nb078_alpha_dummy_959), (nb078_alpha_dummy_960 h)), ((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0406 x y h)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_957), (nb078_alpha_dummy_958 h)), ((nb078_alpha_dummy_926), (nb078_alpha_dummy_928 h)), ((nb078_alpha_dummy_925), (nb078_alpha_dummy_927 h)), ((nb078_alpha_dummy_955), (nb078_alpha_dummy_956 h)), ((nb078_alpha_dummy_929), (nb078_alpha_dummy_930 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (nb078_wpp_refl_0407 x y h)))))))

theorem nb078_compact_fv_empty_0726 : (nb078_alpha_dummy_962) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2430 : (nb078_alpha_dummy_962) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_962, fv_syn_cvv] using (nb078_compact_fv_empty_0726)

theorem nb078_compact_fv_empty_0727 (h : Var) : (nb078_alpha_dummy_964 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2431 (h : Var) : (nb078_alpha_dummy_964 h) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_964, fv_syn_cvv] using (nb078_compact_fv_empty_0727 h)

theorem nb078_compact_fv_empty_0728 : (nb078_alpha_dummy_961) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2432 : (nb078_alpha_dummy_961) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_961, fv_syn_cvv] using (nb078_compact_fv_empty_0728)

theorem nb078_compact_fv_empty_0729 (h : Var) : (nb078_alpha_dummy_963 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2433 (h : Var) : (nb078_alpha_dummy_963 h) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_963, fv_syn_cvv] using (nb078_compact_fv_empty_0729 h)

theorem nb078_wpp_notmem_2434 : (nb078_alpha_dummy_002) ∉ ((syn_cvv)).fv := by
  simpa only [nb078_alpha_dummy_002, fv_syn_cvv] using (nb078_compact_fv_empty_0606)

theorem nb078_wpp_notmem_2435 (h : Var) : h ∉ ((syn_cvv)).fv := by
  simpa only [fv_syn_cvv] using (nb078_compact_fv_empty_0607 h)

theorem nb078_compact_envfresh_0408 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_962) (nb078_alpha_dummy_964 h) (nb078_wpp_notmem_2430) (nb078_wpp_notmem_2431 h) (TEnvFresh.consFresh (nb078_alpha_dummy_961) (nb078_alpha_dummy_963 h) (nb078_wpp_notmem_2432) (nb078_wpp_notmem_2433 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2434) (nb078_wpp_notmem_2435 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0522) (nb078_wpp_notmem_0523 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0524) (nb078_wpp_notmem_0525 x) (TEnvFresh.nil ((syn_cvv)).fv))))))

noncomputable def nb078_wpp_refl_0408 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0408 x y h)

theorem nb078_compact_fv_empty_0730 : (nb078_alpha_dummy_981) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2436 : (nb078_alpha_dummy_981) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_981, fv_syn_c1c] using (nb078_compact_fv_empty_0730)

theorem nb078_compact_fv_empty_0731 (h : Var) : (nb078_alpha_dummy_984 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2437 (h : Var) : (nb078_alpha_dummy_984 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_984, fv_syn_c1c] using (nb078_compact_fv_empty_0731 h)

theorem nb078_compact_fv_empty_0732 : (nb078_alpha_dummy_980) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2438 : (nb078_alpha_dummy_980) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_980, fv_syn_c1c] using (nb078_compact_fv_empty_0732)

theorem nb078_compact_fv_empty_0733 (h : Var) : (nb078_alpha_dummy_983 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2439 (h : Var) : (nb078_alpha_dummy_983 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_983, fv_syn_c1c] using (nb078_compact_fv_empty_0733 h)

theorem nb078_compact_fv_empty_0734 : (nb078_alpha_dummy_979) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2440 : (nb078_alpha_dummy_979) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_979, fv_syn_c1c] using (nb078_compact_fv_empty_0734)

theorem nb078_compact_fv_empty_0735 (h : Var) : (nb078_alpha_dummy_982 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2441 (h : Var) : (nb078_alpha_dummy_982 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_982, fv_syn_c1c] using (nb078_compact_fv_empty_0735 h)

theorem nb078_compact_fv_empty_0736 : (nb078_alpha_dummy_977) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2442 : (nb078_alpha_dummy_977) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_977, fv_syn_c1c] using (nb078_compact_fv_empty_0736)

theorem nb078_compact_fv_empty_0737 (h : Var) : (nb078_alpha_dummy_978 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2443 (h : Var) : (nb078_alpha_dummy_978 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_978, fv_syn_c1c] using (nb078_compact_fv_empty_0737 h)

theorem nb078_compact_fv_empty_0738 : (nb078_alpha_dummy_973) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2444 : (nb078_alpha_dummy_973) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_973, fv_syn_c1c] using (nb078_compact_fv_empty_0738)

theorem nb078_compact_fv_empty_0739 (h : Var) : (nb078_alpha_dummy_975 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2445 (h : Var) : (nb078_alpha_dummy_975 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_975, fv_syn_c1c] using (nb078_compact_fv_empty_0739 h)

theorem nb078_compact_fv_empty_0740 : (nb078_alpha_dummy_974) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2446 : (nb078_alpha_dummy_974) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_974, fv_syn_c1c] using (nb078_compact_fv_empty_0740)

theorem nb078_compact_fv_empty_0741 (h : Var) : (nb078_alpha_dummy_976 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2447 (h : Var) : (nb078_alpha_dummy_976 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_976, fv_syn_c1c] using (nb078_compact_fv_empty_0741 h)

theorem nb078_compact_fv_empty_0742 : (nb078_alpha_dummy_966) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2448 : (nb078_alpha_dummy_966) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_966, fv_syn_c1c] using (nb078_compact_fv_empty_0742)

theorem nb078_compact_fv_empty_0743 (h : Var) : (nb078_alpha_dummy_968 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2449 (h : Var) : (nb078_alpha_dummy_968 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_968, fv_syn_c1c] using (nb078_compact_fv_empty_0743 h)

theorem nb078_compact_fv_empty_0744 : (nb078_alpha_dummy_965) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2450 : (nb078_alpha_dummy_965) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_965, fv_syn_c1c] using (nb078_compact_fv_empty_0744)

theorem nb078_compact_fv_empty_0745 (h : Var) : (nb078_alpha_dummy_967 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2451 (h : Var) : (nb078_alpha_dummy_967 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_967, fv_syn_c1c] using (nb078_compact_fv_empty_0745 h)

theorem nb078_compact_fv_empty_0746 : (nb078_alpha_dummy_971) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2452 : (nb078_alpha_dummy_971) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_971, fv_syn_c1c] using (nb078_compact_fv_empty_0746)

theorem nb078_compact_fv_empty_0747 (h : Var) : (nb078_alpha_dummy_972 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2453 (h : Var) : (nb078_alpha_dummy_972 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_972, fv_syn_c1c] using (nb078_compact_fv_empty_0747 h)

theorem nb078_compact_fv_empty_0748 : (nb078_alpha_dummy_969) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2454 : (nb078_alpha_dummy_969) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_969, fv_syn_c1c] using (nb078_compact_fv_empty_0748)

theorem nb078_compact_fv_empty_0749 (h : Var) : (nb078_alpha_dummy_970 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2455 (h : Var) : (nb078_alpha_dummy_970 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_970, fv_syn_c1c] using (nb078_compact_fv_empty_0749 h)

theorem nb078_wpp_notmem_2456 : (nb078_alpha_dummy_962) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_962, fv_syn_c1c] using (nb078_compact_fv_empty_0726)

theorem nb078_wpp_notmem_2457 (h : Var) : (nb078_alpha_dummy_964 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_964, fv_syn_c1c] using (nb078_compact_fv_empty_0727 h)

theorem nb078_wpp_notmem_2458 : (nb078_alpha_dummy_961) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_961, fv_syn_c1c] using (nb078_compact_fv_empty_0728)

theorem nb078_wpp_notmem_2459 (h : Var) : (nb078_alpha_dummy_963 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_963, fv_syn_c1c] using (nb078_compact_fv_empty_0729 h)

theorem nb078_compact_envfresh_0409 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980), (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)), ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_981) (nb078_alpha_dummy_984 h) (nb078_wpp_notmem_2436) (nb078_wpp_notmem_2437 h) (TEnvFresh.consFresh (nb078_alpha_dummy_980) (nb078_alpha_dummy_983 h) (nb078_wpp_notmem_2438) (nb078_wpp_notmem_2439 h) (TEnvFresh.consFresh (nb078_alpha_dummy_979) (nb078_alpha_dummy_982 h) (nb078_wpp_notmem_2440) (nb078_wpp_notmem_2441 h) (TEnvFresh.consFresh (nb078_alpha_dummy_977) (nb078_alpha_dummy_978 h) (nb078_wpp_notmem_2442) (nb078_wpp_notmem_2443 h) (TEnvFresh.consFresh (nb078_alpha_dummy_973) (nb078_alpha_dummy_975 h) (nb078_wpp_notmem_2444) (nb078_wpp_notmem_2445 h) (TEnvFresh.consFresh (nb078_alpha_dummy_974) (nb078_alpha_dummy_976 h) (nb078_wpp_notmem_2446) (nb078_wpp_notmem_2447 h) (TEnvFresh.consFresh (nb078_alpha_dummy_966) (nb078_alpha_dummy_968 h) (nb078_wpp_notmem_2448) (nb078_wpp_notmem_2449 h) (TEnvFresh.consFresh (nb078_alpha_dummy_965) (nb078_alpha_dummy_967 h) (nb078_wpp_notmem_2450) (nb078_wpp_notmem_2451 h) (TEnvFresh.consFresh (nb078_alpha_dummy_971) (nb078_alpha_dummy_972 h) (nb078_wpp_notmem_2452) (nb078_wpp_notmem_2453 h) (TEnvFresh.consFresh (nb078_alpha_dummy_969) (nb078_alpha_dummy_970 h) (nb078_wpp_notmem_2454) (nb078_wpp_notmem_2455 h) (TEnvFresh.consFresh (nb078_alpha_dummy_962) (nb078_alpha_dummy_964 h) (nb078_wpp_notmem_2456) (nb078_wpp_notmem_2457 h) (TEnvFresh.consFresh (nb078_alpha_dummy_961) (nb078_alpha_dummy_963 h) (nb078_wpp_notmem_2458) (nb078_wpp_notmem_2459 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0409 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980), (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)), ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0409 x y h)

theorem nb078_wpp_notmem_2460 : (nb078_alpha_dummy_981) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_981, fv_syn_c0] using (nb078_compact_fv_empty_0730)

theorem nb078_wpp_notmem_2461 (h : Var) : (nb078_alpha_dummy_984 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_984, fv_syn_c0] using (nb078_compact_fv_empty_0731 h)

theorem nb078_wpp_notmem_2462 : (nb078_alpha_dummy_980) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_980, fv_syn_c0] using (nb078_compact_fv_empty_0732)

theorem nb078_wpp_notmem_2463 (h : Var) : (nb078_alpha_dummy_983 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_983, fv_syn_c0] using (nb078_compact_fv_empty_0733 h)

theorem nb078_wpp_notmem_2464 : (nb078_alpha_dummy_979) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_979, fv_syn_c0] using (nb078_compact_fv_empty_0734)

theorem nb078_wpp_notmem_2465 (h : Var) : (nb078_alpha_dummy_982 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_982, fv_syn_c0] using (nb078_compact_fv_empty_0735 h)

theorem nb078_wpp_notmem_2466 : (nb078_alpha_dummy_977) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_977, fv_syn_c0] using (nb078_compact_fv_empty_0736)

theorem nb078_wpp_notmem_2467 (h : Var) : (nb078_alpha_dummy_978 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_978, fv_syn_c0] using (nb078_compact_fv_empty_0737 h)

theorem nb078_wpp_notmem_2468 : (nb078_alpha_dummy_973) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_973, fv_syn_c0] using (nb078_compact_fv_empty_0738)

theorem nb078_wpp_notmem_2469 (h : Var) : (nb078_alpha_dummy_975 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_975, fv_syn_c0] using (nb078_compact_fv_empty_0739 h)

theorem nb078_wpp_notmem_2470 : (nb078_alpha_dummy_974) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_974, fv_syn_c0] using (nb078_compact_fv_empty_0740)

theorem nb078_wpp_notmem_2471 (h : Var) : (nb078_alpha_dummy_976 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_976, fv_syn_c0] using (nb078_compact_fv_empty_0741 h)

theorem nb078_wpp_notmem_2472 : (nb078_alpha_dummy_966) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_966, fv_syn_c0] using (nb078_compact_fv_empty_0742)

theorem nb078_wpp_notmem_2473 (h : Var) : (nb078_alpha_dummy_968 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_968, fv_syn_c0] using (nb078_compact_fv_empty_0743 h)

theorem nb078_wpp_notmem_2474 : (nb078_alpha_dummy_965) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_965, fv_syn_c0] using (nb078_compact_fv_empty_0744)

theorem nb078_wpp_notmem_2475 (h : Var) : (nb078_alpha_dummy_967 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_967, fv_syn_c0] using (nb078_compact_fv_empty_0745 h)

theorem nb078_wpp_notmem_2476 : (nb078_alpha_dummy_971) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_971, fv_syn_c0] using (nb078_compact_fv_empty_0746)

theorem nb078_wpp_notmem_2477 (h : Var) : (nb078_alpha_dummy_972 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_972, fv_syn_c0] using (nb078_compact_fv_empty_0747 h)

theorem nb078_wpp_notmem_2478 : (nb078_alpha_dummy_969) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_969, fv_syn_c0] using (nb078_compact_fv_empty_0748)

theorem nb078_wpp_notmem_2479 (h : Var) : (nb078_alpha_dummy_970 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_970, fv_syn_c0] using (nb078_compact_fv_empty_0749 h)

theorem nb078_wpp_notmem_2480 : (nb078_alpha_dummy_962) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_962, fv_syn_c0] using (nb078_compact_fv_empty_0726)

theorem nb078_wpp_notmem_2481 (h : Var) : (nb078_alpha_dummy_964 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_964, fv_syn_c0] using (nb078_compact_fv_empty_0727 h)

theorem nb078_wpp_notmem_2482 : (nb078_alpha_dummy_961) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_961, fv_syn_c0] using (nb078_compact_fv_empty_0728)

theorem nb078_wpp_notmem_2483 (h : Var) : (nb078_alpha_dummy_963 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_963, fv_syn_c0] using (nb078_compact_fv_empty_0729 h)

theorem nb078_compact_envfresh_0410 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980), (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)), ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_981) (nb078_alpha_dummy_984 h) (nb078_wpp_notmem_2460) (nb078_wpp_notmem_2461 h) (TEnvFresh.consFresh (nb078_alpha_dummy_980) (nb078_alpha_dummy_983 h) (nb078_wpp_notmem_2462) (nb078_wpp_notmem_2463 h) (TEnvFresh.consFresh (nb078_alpha_dummy_979) (nb078_alpha_dummy_982 h) (nb078_wpp_notmem_2464) (nb078_wpp_notmem_2465 h) (TEnvFresh.consFresh (nb078_alpha_dummy_977) (nb078_alpha_dummy_978 h) (nb078_wpp_notmem_2466) (nb078_wpp_notmem_2467 h) (TEnvFresh.consFresh (nb078_alpha_dummy_973) (nb078_alpha_dummy_975 h) (nb078_wpp_notmem_2468) (nb078_wpp_notmem_2469 h) (TEnvFresh.consFresh (nb078_alpha_dummy_974) (nb078_alpha_dummy_976 h) (nb078_wpp_notmem_2470) (nb078_wpp_notmem_2471 h) (TEnvFresh.consFresh (nb078_alpha_dummy_966) (nb078_alpha_dummy_968 h) (nb078_wpp_notmem_2472) (nb078_wpp_notmem_2473 h) (TEnvFresh.consFresh (nb078_alpha_dummy_965) (nb078_alpha_dummy_967 h) (nb078_wpp_notmem_2474) (nb078_wpp_notmem_2475 h) (TEnvFresh.consFresh (nb078_alpha_dummy_971) (nb078_alpha_dummy_972 h) (nb078_wpp_notmem_2476) (nb078_wpp_notmem_2477 h) (TEnvFresh.consFresh (nb078_alpha_dummy_969) (nb078_alpha_dummy_970 h) (nb078_wpp_notmem_2478) (nb078_wpp_notmem_2479 h) (TEnvFresh.consFresh (nb078_alpha_dummy_962) (nb078_alpha_dummy_964 h) (nb078_wpp_notmem_2480) (nb078_wpp_notmem_2481 h) (TEnvFresh.consFresh (nb078_alpha_dummy_961) (nb078_alpha_dummy_963 h) (nb078_wpp_notmem_2482) (nb078_wpp_notmem_2483 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0410 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980), (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)), ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0410 x y h)

theorem nb078_wpp_notmem_2484 : (nb078_alpha_dummy_977) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_977, fv_syn_cnnc] using (nb078_compact_fv_empty_0736)

theorem nb078_wpp_notmem_2485 (h : Var) : (nb078_alpha_dummy_978 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_978, fv_syn_cnnc] using (nb078_compact_fv_empty_0737 h)

theorem nb078_wpp_notmem_2486 : (nb078_alpha_dummy_973) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_973, fv_syn_cnnc] using (nb078_compact_fv_empty_0738)

theorem nb078_wpp_notmem_2487 (h : Var) : (nb078_alpha_dummy_975 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_975, fv_syn_cnnc] using (nb078_compact_fv_empty_0739 h)

theorem nb078_wpp_notmem_2488 : (nb078_alpha_dummy_974) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_974, fv_syn_cnnc] using (nb078_compact_fv_empty_0740)

theorem nb078_wpp_notmem_2489 (h : Var) : (nb078_alpha_dummy_976 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_976, fv_syn_cnnc] using (nb078_compact_fv_empty_0741 h)

theorem nb078_wpp_notmem_2490 : (nb078_alpha_dummy_966) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_966, fv_syn_cnnc] using (nb078_compact_fv_empty_0742)

theorem nb078_wpp_notmem_2491 (h : Var) : (nb078_alpha_dummy_968 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_968, fv_syn_cnnc] using (nb078_compact_fv_empty_0743 h)

theorem nb078_wpp_notmem_2492 : (nb078_alpha_dummy_965) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_965, fv_syn_cnnc] using (nb078_compact_fv_empty_0744)

theorem nb078_wpp_notmem_2493 (h : Var) : (nb078_alpha_dummy_967 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_967, fv_syn_cnnc] using (nb078_compact_fv_empty_0745 h)

theorem nb078_wpp_notmem_2494 : (nb078_alpha_dummy_971) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_971, fv_syn_cnnc] using (nb078_compact_fv_empty_0746)

theorem nb078_wpp_notmem_2495 (h : Var) : (nb078_alpha_dummy_972 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_972, fv_syn_cnnc] using (nb078_compact_fv_empty_0747 h)

theorem nb078_wpp_notmem_2496 : (nb078_alpha_dummy_969) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_969, fv_syn_cnnc] using (nb078_compact_fv_empty_0748)

theorem nb078_wpp_notmem_2497 (h : Var) : (nb078_alpha_dummy_970 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_970, fv_syn_cnnc] using (nb078_compact_fv_empty_0749 h)

theorem nb078_wpp_notmem_2498 : (nb078_alpha_dummy_962) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_962, fv_syn_cnnc] using (nb078_compact_fv_empty_0726)

theorem nb078_wpp_notmem_2499 (h : Var) : (nb078_alpha_dummy_964 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_964, fv_syn_cnnc] using (nb078_compact_fv_empty_0727 h)

theorem nb078_wpp_notmem_2500 : (nb078_alpha_dummy_961) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_961, fv_syn_cnnc] using (nb078_compact_fv_empty_0728)

theorem nb078_wpp_notmem_2501 (h : Var) : (nb078_alpha_dummy_963 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_963, fv_syn_cnnc] using (nb078_compact_fv_empty_0729 h)

theorem nb078_compact_envfresh_0411 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_977) (nb078_alpha_dummy_978 h) (nb078_wpp_notmem_2484) (nb078_wpp_notmem_2485 h) (TEnvFresh.consFresh (nb078_alpha_dummy_973) (nb078_alpha_dummy_975 h) (nb078_wpp_notmem_2486) (nb078_wpp_notmem_2487 h) (TEnvFresh.consFresh (nb078_alpha_dummy_974) (nb078_alpha_dummy_976 h) (nb078_wpp_notmem_2488) (nb078_wpp_notmem_2489 h) (TEnvFresh.consFresh (nb078_alpha_dummy_966) (nb078_alpha_dummy_968 h) (nb078_wpp_notmem_2490) (nb078_wpp_notmem_2491 h) (TEnvFresh.consFresh (nb078_alpha_dummy_965) (nb078_alpha_dummy_967 h) (nb078_wpp_notmem_2492) (nb078_wpp_notmem_2493 h) (TEnvFresh.consFresh (nb078_alpha_dummy_971) (nb078_alpha_dummy_972 h) (nb078_wpp_notmem_2494) (nb078_wpp_notmem_2495 h) (TEnvFresh.consFresh (nb078_alpha_dummy_969) (nb078_alpha_dummy_970 h) (nb078_wpp_notmem_2496) (nb078_wpp_notmem_2497 h) (TEnvFresh.consFresh (nb078_alpha_dummy_962) (nb078_alpha_dummy_964 h) (nb078_wpp_notmem_2498) (nb078_wpp_notmem_2499 h) (TEnvFresh.consFresh (nb078_alpha_dummy_961) (nb078_alpha_dummy_963 h) (nb078_wpp_notmem_2500) (nb078_wpp_notmem_2501 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb078_wpp_refl_0411 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_971), (nb078_alpha_dummy_972 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0411 x y h)

theorem nb078_compact_fv_empty_0750 : (nb078_alpha_dummy_999) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2502 : (nb078_alpha_dummy_999) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_999, fv_syn_c1c] using (nb078_compact_fv_empty_0750)

theorem nb078_compact_fv_empty_0751 (h : Var) : (nb078_alpha_dummy_1000 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2503 (h : Var) : (nb078_alpha_dummy_1000 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0751 h)

theorem nb078_compact_fv_empty_0752 : (nb078_alpha_dummy_997) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2504 : (nb078_alpha_dummy_997) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_997, fv_syn_c1c] using (nb078_compact_fv_empty_0752)

theorem nb078_compact_fv_empty_0753 (h : Var) : (nb078_alpha_dummy_998 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2505 (h : Var) : (nb078_alpha_dummy_998 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_998, fv_syn_c1c] using (nb078_compact_fv_empty_0753 h)

theorem nb078_compact_fv_empty_0754 : (nb078_alpha_dummy_995) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2506 : (nb078_alpha_dummy_995) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_995, fv_syn_c1c] using (nb078_compact_fv_empty_0754)

theorem nb078_compact_fv_empty_0755 (h : Var) : (nb078_alpha_dummy_996 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2507 (h : Var) : (nb078_alpha_dummy_996 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_996, fv_syn_c1c] using (nb078_compact_fv_empty_0755 h)

theorem nb078_compact_envfresh_0412 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980), (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)), ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)), ((nb078_alpha_dummy_997), (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_995), (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_981) (nb078_alpha_dummy_984 h) (nb078_wpp_notmem_2436) (nb078_wpp_notmem_2437 h) (TEnvFresh.consFresh (nb078_alpha_dummy_980) (nb078_alpha_dummy_983 h) (nb078_wpp_notmem_2438) (nb078_wpp_notmem_2439 h) (TEnvFresh.consFresh (nb078_alpha_dummy_979) (nb078_alpha_dummy_982 h) (nb078_wpp_notmem_2440) (nb078_wpp_notmem_2441 h) (TEnvFresh.consFresh (nb078_alpha_dummy_977) (nb078_alpha_dummy_978 h) (nb078_wpp_notmem_2442) (nb078_wpp_notmem_2443 h) (TEnvFresh.consFresh (nb078_alpha_dummy_973) (nb078_alpha_dummy_975 h) (nb078_wpp_notmem_2444) (nb078_wpp_notmem_2445 h) (TEnvFresh.consFresh (nb078_alpha_dummy_974) (nb078_alpha_dummy_976 h) (nb078_wpp_notmem_2446) (nb078_wpp_notmem_2447 h) (TEnvFresh.consFresh (nb078_alpha_dummy_999) (nb078_alpha_dummy_1000 h) (nb078_wpp_notmem_2502) (nb078_wpp_notmem_2503 h) (TEnvFresh.consFresh (nb078_alpha_dummy_997) (nb078_alpha_dummy_998 h) (nb078_wpp_notmem_2504) (nb078_wpp_notmem_2505 h) (TEnvFresh.consFresh (nb078_alpha_dummy_966) (nb078_alpha_dummy_968 h) (nb078_wpp_notmem_2448) (nb078_wpp_notmem_2449 h) (TEnvFresh.consFresh (nb078_alpha_dummy_965) (nb078_alpha_dummy_967 h) (nb078_wpp_notmem_2450) (nb078_wpp_notmem_2451 h) (TEnvFresh.consFresh (nb078_alpha_dummy_995) (nb078_alpha_dummy_996 h) (nb078_wpp_notmem_2506) (nb078_wpp_notmem_2507 h) (TEnvFresh.consFresh (nb078_alpha_dummy_969) (nb078_alpha_dummy_970 h) (nb078_wpp_notmem_2454) (nb078_wpp_notmem_2455 h) (TEnvFresh.consFresh (nb078_alpha_dummy_962) (nb078_alpha_dummy_964 h) (nb078_wpp_notmem_2456) (nb078_wpp_notmem_2457 h) (TEnvFresh.consFresh (nb078_alpha_dummy_961) (nb078_alpha_dummy_963 h) (nb078_wpp_notmem_2458) (nb078_wpp_notmem_2459 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0412 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_981), (nb078_alpha_dummy_984 h)), ((nb078_alpha_dummy_980), (nb078_alpha_dummy_983 h)), ((nb078_alpha_dummy_979), (nb078_alpha_dummy_982 h)), ((nb078_alpha_dummy_977), (nb078_alpha_dummy_978 h)), ((nb078_alpha_dummy_973), (nb078_alpha_dummy_975 h)), ((nb078_alpha_dummy_974), (nb078_alpha_dummy_976 h)), ((nb078_alpha_dummy_999), (nb078_alpha_dummy_1000 h)), ((nb078_alpha_dummy_997), (nb078_alpha_dummy_998 h)), ((nb078_alpha_dummy_966), (nb078_alpha_dummy_968 h)), ((nb078_alpha_dummy_965), (nb078_alpha_dummy_967 h)), ((nb078_alpha_dummy_995), (nb078_alpha_dummy_996 h)), ((nb078_alpha_dummy_969), (nb078_alpha_dummy_970 h)), ((nb078_alpha_dummy_962), (nb078_alpha_dummy_964 h)), ((nb078_alpha_dummy_961), (nb078_alpha_dummy_963 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0412 x y h)

theorem nb078_wpp_notmem_2508 : (nb078_alpha_dummy_999) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_999, fv_syn_c0] using (nb078_compact_fv_empty_0750)

theorem nb078_wpp_notmem_2509 (h : Var) : (nb078_alpha_dummy_1000 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0751 h)

theorem nb078_wpp_notmem_2510 : (nb078_alpha_dummy_997) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_997, fv_syn_c0] using (nb078_compact_fv_empty_0752)

theorem nb078_wpp_notmem_2511 (h : Var) : (nb078_alpha_dummy_998 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_998, fv_syn_c0] using (nb078_compact_fv_empty_0753 h)

theorem nb078_wpp_notmem_2512 : (nb078_alpha_dummy_995) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_995, fv_syn_c0] using (nb078_compact_fv_empty_0754)

theorem nb078_wpp_notmem_2513 (h : Var) : (nb078_alpha_dummy_996 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_996, fv_syn_c0] using (nb078_compact_fv_empty_0755 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
