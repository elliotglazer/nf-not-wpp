import NAR4C078C001Part129

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

noncomputable def nb078_split_alpha_0107 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_887)) (syn_cphi (Class.cv (nb078_alpha_dummy_854)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_887)) (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_888 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_888 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0889 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0889 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0918) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0919 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0916) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0917 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0892) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0893 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0892) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0893 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0890) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0891 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0354 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0896) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0897 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0894) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0895 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0900) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0901 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0898) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0899 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0896) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0897 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0894) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0895 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0900) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0901 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0898) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0899 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0355 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0904) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0905 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0902) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0903 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0904) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0905 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0902) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0903 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0908) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0909 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0906) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0907 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0908) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0909 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0906) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0907 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0890) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0891 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0356 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0890) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0891 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0890) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0891 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0356 x y h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0889 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0888) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0889 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0918) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0919 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0916) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0917 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_854))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_856 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0892) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0893 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0892) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0893 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0890) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0891 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0354 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0896) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0897 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0894) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0895 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0900) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0901 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0898) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0899 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0896) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0897 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0894) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0895 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0900) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0901 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0898) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0899 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0355 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0904) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0905 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0902) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0903 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0904) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0905 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0902) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0903 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0908) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0909 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0906) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0907 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0908) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0909 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0906) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0907 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0890) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0891 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0356 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0890) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0891 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0890) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0891 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_887), (nb078_alpha_dummy_888 h)), ((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0356 x y h))))))))))))))))))))

theorem nb078_wpp_notmem_2244 : (nb078_alpha_dummy_885) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_885, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0670)

theorem nb078_wpp_notmem_2245 (h : Var) : (nb078_alpha_dummy_886 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_886, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0671 h)

theorem nb078_wpp_notmem_2246 : (nb078_alpha_dummy_854) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_854, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0654)

theorem nb078_wpp_notmem_2247 (h : Var) : (nb078_alpha_dummy_856 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_856, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0655 h)

theorem nb078_wpp_notmem_2248 : (nb078_alpha_dummy_853) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_853, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0656)

theorem nb078_wpp_notmem_2249 (h : Var) : (nb078_alpha_dummy_855 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_855, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0657 h)

theorem nb078_wpp_notmem_2250 : (nb078_alpha_dummy_883) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_883, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0672)

theorem nb078_wpp_notmem_2251 (h : Var) : (nb078_alpha_dummy_884 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_884, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0673 h)

theorem nb078_wpp_notmem_2252 : (nb078_alpha_dummy_857) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_857, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0660)

theorem nb078_wpp_notmem_2253 (h : Var) : (nb078_alpha_dummy_858 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_858, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0661 h)

theorem nb078_wpp_notmem_2254 : (nb078_alpha_dummy_848) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_848, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0662)

theorem nb078_wpp_notmem_2255 (h : Var) : (nb078_alpha_dummy_850 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_850, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0663 h)

theorem nb078_wpp_notmem_2256 : (nb078_alpha_dummy_847) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_847, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0664)

theorem nb078_wpp_notmem_2257 (h : Var) : (nb078_alpha_dummy_849 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_849, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0665 h)

theorem nb078_wpp_notmem_2258 : (nb078_alpha_dummy_851) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_851, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0666)

theorem nb078_wpp_notmem_2259 (h : Var) : (nb078_alpha_dummy_852 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_852, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0667 h)

theorem nb078_compact_envfresh_0357 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_885) (nb078_alpha_dummy_886 h) (nb078_wpp_notmem_2244) (nb078_wpp_notmem_2245 h) (TEnvFresh.consFresh (nb078_alpha_dummy_854) (nb078_alpha_dummy_856 h) (nb078_wpp_notmem_2246) (nb078_wpp_notmem_2247 h) (TEnvFresh.consFresh (nb078_alpha_dummy_853) (nb078_alpha_dummy_855 h) (nb078_wpp_notmem_2248) (nb078_wpp_notmem_2249 h) (TEnvFresh.consFresh (nb078_alpha_dummy_883) (nb078_alpha_dummy_884 h) (nb078_wpp_notmem_2250) (nb078_wpp_notmem_2251 h) (TEnvFresh.consFresh (nb078_alpha_dummy_857) (nb078_alpha_dummy_858 h) (nb078_wpp_notmem_2252) (nb078_wpp_notmem_2253 h) (TEnvFresh.consFresh (nb078_alpha_dummy_848) (nb078_alpha_dummy_850 h) (nb078_wpp_notmem_2254) (nb078_wpp_notmem_2255 h) (TEnvFresh.consFresh (nb078_alpha_dummy_847) (nb078_alpha_dummy_849 h) (nb078_wpp_notmem_2256) (nb078_wpp_notmem_2257 h) (TEnvFresh.consFresh (nb078_alpha_dummy_851) (nb078_alpha_dummy_852 h) (nb078_wpp_notmem_2258) (nb078_wpp_notmem_2259 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2152) (nb078_wpp_notmem_2153 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_2052) (nb078_wpp_notmem_2053 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_2054) (nb078_wpp_notmem_2055 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_2056) (nb078_wpp_notmem_2057 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_2058) (nb078_wpp_notmem_2059 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_2060) (nb078_wpp_notmem_2061 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2062) (nb078_wpp_notmem_2063 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0357 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_885), (nb078_alpha_dummy_886 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_883), (nb078_alpha_dummy_884 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0357 x y h)

theorem nb078_compact_fv_empty_0674 : (nb078_alpha_dummy_905) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2260 : (nb078_alpha_dummy_905) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_905, fv_syn_c1c] using (nb078_compact_fv_empty_0674)

theorem nb078_compact_fv_empty_0675 (h : Var) : (nb078_alpha_dummy_908 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2261 (h : Var) : (nb078_alpha_dummy_908 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_908, fv_syn_c1c] using (nb078_compact_fv_empty_0675 h)

theorem nb078_compact_fv_empty_0676 : (nb078_alpha_dummy_904) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2262 : (nb078_alpha_dummy_904) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_904, fv_syn_c1c] using (nb078_compact_fv_empty_0676)

theorem nb078_compact_fv_empty_0677 (h : Var) : (nb078_alpha_dummy_907 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2263 (h : Var) : (nb078_alpha_dummy_907 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_907, fv_syn_c1c] using (nb078_compact_fv_empty_0677 h)

theorem nb078_compact_fv_empty_0678 : (nb078_alpha_dummy_903) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2264 : (nb078_alpha_dummy_903) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_903, fv_syn_c1c] using (nb078_compact_fv_empty_0678)

theorem nb078_compact_fv_empty_0679 (h : Var) : (nb078_alpha_dummy_906 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2265 (h : Var) : (nb078_alpha_dummy_906 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_906, fv_syn_c1c] using (nb078_compact_fv_empty_0679 h)

theorem nb078_compact_fv_empty_0680 : (nb078_alpha_dummy_901) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2266 : (nb078_alpha_dummy_901) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_901, fv_syn_c1c] using (nb078_compact_fv_empty_0680)

theorem nb078_compact_fv_empty_0681 (h : Var) : (nb078_alpha_dummy_902 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2267 (h : Var) : (nb078_alpha_dummy_902 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_902, fv_syn_c1c] using (nb078_compact_fv_empty_0681 h)

theorem nb078_compact_fv_empty_0682 : (nb078_alpha_dummy_897) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2268 : (nb078_alpha_dummy_897) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_897, fv_syn_c1c] using (nb078_compact_fv_empty_0682)

theorem nb078_compact_fv_empty_0683 (h : Var) : (nb078_alpha_dummy_899 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2269 (h : Var) : (nb078_alpha_dummy_899 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_899, fv_syn_c1c] using (nb078_compact_fv_empty_0683 h)

theorem nb078_compact_fv_empty_0684 : (nb078_alpha_dummy_898) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2270 : (nb078_alpha_dummy_898) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_898, fv_syn_c1c] using (nb078_compact_fv_empty_0684)

theorem nb078_compact_fv_empty_0685 (h : Var) : (nb078_alpha_dummy_900 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2271 (h : Var) : (nb078_alpha_dummy_900 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_900, fv_syn_c1c] using (nb078_compact_fv_empty_0685 h)

theorem nb078_compact_fv_empty_0686 : (nb078_alpha_dummy_890) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2272 : (nb078_alpha_dummy_890) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_890, fv_syn_c1c] using (nb078_compact_fv_empty_0686)

theorem nb078_compact_fv_empty_0687 (h : Var) : (nb078_alpha_dummy_892 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2273 (h : Var) : (nb078_alpha_dummy_892 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_892, fv_syn_c1c] using (nb078_compact_fv_empty_0687 h)

theorem nb078_compact_fv_empty_0688 : (nb078_alpha_dummy_889) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2274 : (nb078_alpha_dummy_889) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_889, fv_syn_c1c] using (nb078_compact_fv_empty_0688)

theorem nb078_compact_fv_empty_0689 (h : Var) : (nb078_alpha_dummy_891 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2275 (h : Var) : (nb078_alpha_dummy_891 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_891, fv_syn_c1c] using (nb078_compact_fv_empty_0689 h)

theorem nb078_compact_fv_empty_0690 : (nb078_alpha_dummy_895) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2276 : (nb078_alpha_dummy_895) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_895, fv_syn_c1c] using (nb078_compact_fv_empty_0690)

theorem nb078_compact_fv_empty_0691 (h : Var) : (nb078_alpha_dummy_896 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2277 (h : Var) : (nb078_alpha_dummy_896 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_896, fv_syn_c1c] using (nb078_compact_fv_empty_0691 h)

theorem nb078_compact_fv_empty_0692 : (nb078_alpha_dummy_893) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2278 : (nb078_alpha_dummy_893) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_893, fv_syn_c1c] using (nb078_compact_fv_empty_0692)

theorem nb078_compact_fv_empty_0693 (h : Var) : (nb078_alpha_dummy_894 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2279 (h : Var) : (nb078_alpha_dummy_894 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_894, fv_syn_c1c] using (nb078_compact_fv_empty_0693 h)

theorem nb078_compact_envfresh_0358 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_905) (nb078_alpha_dummy_908 h) (nb078_wpp_notmem_2260) (nb078_wpp_notmem_2261 h) (TEnvFresh.consFresh (nb078_alpha_dummy_904) (nb078_alpha_dummy_907 h) (nb078_wpp_notmem_2262) (nb078_wpp_notmem_2263 h) (TEnvFresh.consFresh (nb078_alpha_dummy_903) (nb078_alpha_dummy_906 h) (nb078_wpp_notmem_2264) (nb078_wpp_notmem_2265 h) (TEnvFresh.consFresh (nb078_alpha_dummy_901) (nb078_alpha_dummy_902 h) (nb078_wpp_notmem_2266) (nb078_wpp_notmem_2267 h) (TEnvFresh.consFresh (nb078_alpha_dummy_897) (nb078_alpha_dummy_899 h) (nb078_wpp_notmem_2268) (nb078_wpp_notmem_2269 h) (TEnvFresh.consFresh (nb078_alpha_dummy_898) (nb078_alpha_dummy_900 h) (nb078_wpp_notmem_2270) (nb078_wpp_notmem_2271 h) (TEnvFresh.consFresh (nb078_alpha_dummy_890) (nb078_alpha_dummy_892 h) (nb078_wpp_notmem_2272) (nb078_wpp_notmem_2273 h) (TEnvFresh.consFresh (nb078_alpha_dummy_889) (nb078_alpha_dummy_891 h) (nb078_wpp_notmem_2274) (nb078_wpp_notmem_2275 h) (TEnvFresh.consFresh (nb078_alpha_dummy_895) (nb078_alpha_dummy_896 h) (nb078_wpp_notmem_2276) (nb078_wpp_notmem_2277 h) (TEnvFresh.consFresh (nb078_alpha_dummy_893) (nb078_alpha_dummy_894 h) (nb078_wpp_notmem_2278) (nb078_wpp_notmem_2279 h) (TEnvFresh.consFresh (nb078_alpha_dummy_848) (nb078_alpha_dummy_850 h) (nb078_wpp_notmem_2174) (nb078_wpp_notmem_2175 h) (TEnvFresh.consFresh (nb078_alpha_dummy_847) (nb078_alpha_dummy_849 h) (nb078_wpp_notmem_2176) (nb078_wpp_notmem_2177 h) (TEnvFresh.consFresh (nb078_alpha_dummy_851) (nb078_alpha_dummy_852 h) (nb078_wpp_notmem_2178) (nb078_wpp_notmem_2179 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2084) (nb078_wpp_notmem_2085 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1954) (nb078_wpp_notmem_1955 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1956) (nb078_wpp_notmem_1957 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1958) (nb078_wpp_notmem_1959 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1960) (nb078_wpp_notmem_1961 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1962) (nb078_wpp_notmem_1963 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0358 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0358 x y h)

theorem nb078_wpp_notmem_2280 : (nb078_alpha_dummy_905) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_905, fv_syn_c0] using (nb078_compact_fv_empty_0674)

theorem nb078_wpp_notmem_2281 (h : Var) : (nb078_alpha_dummy_908 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_908, fv_syn_c0] using (nb078_compact_fv_empty_0675 h)

theorem nb078_wpp_notmem_2282 : (nb078_alpha_dummy_904) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_904, fv_syn_c0] using (nb078_compact_fv_empty_0676)

theorem nb078_wpp_notmem_2283 (h : Var) : (nb078_alpha_dummy_907 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_907, fv_syn_c0] using (nb078_compact_fv_empty_0677 h)

theorem nb078_wpp_notmem_2284 : (nb078_alpha_dummy_903) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_903, fv_syn_c0] using (nb078_compact_fv_empty_0678)

theorem nb078_wpp_notmem_2285 (h : Var) : (nb078_alpha_dummy_906 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_906, fv_syn_c0] using (nb078_compact_fv_empty_0679 h)

theorem nb078_wpp_notmem_2286 : (nb078_alpha_dummy_901) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_901, fv_syn_c0] using (nb078_compact_fv_empty_0680)

theorem nb078_wpp_notmem_2287 (h : Var) : (nb078_alpha_dummy_902 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_902, fv_syn_c0] using (nb078_compact_fv_empty_0681 h)

theorem nb078_wpp_notmem_2288 : (nb078_alpha_dummy_897) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_897, fv_syn_c0] using (nb078_compact_fv_empty_0682)

theorem nb078_wpp_notmem_2289 (h : Var) : (nb078_alpha_dummy_899 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_899, fv_syn_c0] using (nb078_compact_fv_empty_0683 h)

theorem nb078_wpp_notmem_2290 : (nb078_alpha_dummy_898) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_898, fv_syn_c0] using (nb078_compact_fv_empty_0684)

theorem nb078_wpp_notmem_2291 (h : Var) : (nb078_alpha_dummy_900 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_900, fv_syn_c0] using (nb078_compact_fv_empty_0685 h)

theorem nb078_wpp_notmem_2292 : (nb078_alpha_dummy_890) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_890, fv_syn_c0] using (nb078_compact_fv_empty_0686)

theorem nb078_wpp_notmem_2293 (h : Var) : (nb078_alpha_dummy_892 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_892, fv_syn_c0] using (nb078_compact_fv_empty_0687 h)

theorem nb078_wpp_notmem_2294 : (nb078_alpha_dummy_889) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_889, fv_syn_c0] using (nb078_compact_fv_empty_0688)

theorem nb078_wpp_notmem_2295 (h : Var) : (nb078_alpha_dummy_891 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_891, fv_syn_c0] using (nb078_compact_fv_empty_0689 h)

theorem nb078_wpp_notmem_2296 : (nb078_alpha_dummy_895) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_895, fv_syn_c0] using (nb078_compact_fv_empty_0690)

theorem nb078_wpp_notmem_2297 (h : Var) : (nb078_alpha_dummy_896 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_896, fv_syn_c0] using (nb078_compact_fv_empty_0691 h)

theorem nb078_wpp_notmem_2298 : (nb078_alpha_dummy_893) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_893, fv_syn_c0] using (nb078_compact_fv_empty_0692)

theorem nb078_wpp_notmem_2299 (h : Var) : (nb078_alpha_dummy_894 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_894, fv_syn_c0] using (nb078_compact_fv_empty_0693 h)

theorem nb078_compact_envfresh_0359 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_905) (nb078_alpha_dummy_908 h) (nb078_wpp_notmem_2280) (nb078_wpp_notmem_2281 h) (TEnvFresh.consFresh (nb078_alpha_dummy_904) (nb078_alpha_dummy_907 h) (nb078_wpp_notmem_2282) (nb078_wpp_notmem_2283 h) (TEnvFresh.consFresh (nb078_alpha_dummy_903) (nb078_alpha_dummy_906 h) (nb078_wpp_notmem_2284) (nb078_wpp_notmem_2285 h) (TEnvFresh.consFresh (nb078_alpha_dummy_901) (nb078_alpha_dummy_902 h) (nb078_wpp_notmem_2286) (nb078_wpp_notmem_2287 h) (TEnvFresh.consFresh (nb078_alpha_dummy_897) (nb078_alpha_dummy_899 h) (nb078_wpp_notmem_2288) (nb078_wpp_notmem_2289 h) (TEnvFresh.consFresh (nb078_alpha_dummy_898) (nb078_alpha_dummy_900 h) (nb078_wpp_notmem_2290) (nb078_wpp_notmem_2291 h) (TEnvFresh.consFresh (nb078_alpha_dummy_890) (nb078_alpha_dummy_892 h) (nb078_wpp_notmem_2292) (nb078_wpp_notmem_2293 h) (TEnvFresh.consFresh (nb078_alpha_dummy_889) (nb078_alpha_dummy_891 h) (nb078_wpp_notmem_2294) (nb078_wpp_notmem_2295 h) (TEnvFresh.consFresh (nb078_alpha_dummy_895) (nb078_alpha_dummy_896 h) (nb078_wpp_notmem_2296) (nb078_wpp_notmem_2297 h) (TEnvFresh.consFresh (nb078_alpha_dummy_893) (nb078_alpha_dummy_894 h) (nb078_wpp_notmem_2298) (nb078_wpp_notmem_2299 h) (TEnvFresh.consFresh (nb078_alpha_dummy_848) (nb078_alpha_dummy_850 h) (nb078_wpp_notmem_2200) (nb078_wpp_notmem_2201 h) (TEnvFresh.consFresh (nb078_alpha_dummy_847) (nb078_alpha_dummy_849 h) (nb078_wpp_notmem_2202) (nb078_wpp_notmem_2203 h) (TEnvFresh.consFresh (nb078_alpha_dummy_851) (nb078_alpha_dummy_852 h) (nb078_wpp_notmem_2204) (nb078_wpp_notmem_2205 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2106) (nb078_wpp_notmem_2107 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1986) (nb078_wpp_notmem_1987 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1988) (nb078_wpp_notmem_1989 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1990) (nb078_wpp_notmem_1991 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1992) (nb078_wpp_notmem_1993 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1994) (nb078_wpp_notmem_1995 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0359 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_905), (nb078_alpha_dummy_908 h)), ((nb078_alpha_dummy_904), (nb078_alpha_dummy_907 h)), ((nb078_alpha_dummy_903), (nb078_alpha_dummy_906 h)), ((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0359 x y h)

theorem nb078_wpp_notmem_2300 : (nb078_alpha_dummy_901) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_901, fv_syn_cnnc] using (nb078_compact_fv_empty_0680)

theorem nb078_wpp_notmem_2301 (h : Var) : (nb078_alpha_dummy_902 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_902, fv_syn_cnnc] using (nb078_compact_fv_empty_0681 h)

theorem nb078_wpp_notmem_2302 : (nb078_alpha_dummy_897) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_897, fv_syn_cnnc] using (nb078_compact_fv_empty_0682)

theorem nb078_wpp_notmem_2303 (h : Var) : (nb078_alpha_dummy_899 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_899, fv_syn_cnnc] using (nb078_compact_fv_empty_0683 h)

theorem nb078_wpp_notmem_2304 : (nb078_alpha_dummy_898) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_898, fv_syn_cnnc] using (nb078_compact_fv_empty_0684)

theorem nb078_wpp_notmem_2305 (h : Var) : (nb078_alpha_dummy_900 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_900, fv_syn_cnnc] using (nb078_compact_fv_empty_0685 h)

theorem nb078_wpp_notmem_2306 : (nb078_alpha_dummy_890) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_890, fv_syn_cnnc] using (nb078_compact_fv_empty_0686)

theorem nb078_wpp_notmem_2307 (h : Var) : (nb078_alpha_dummy_892 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_892, fv_syn_cnnc] using (nb078_compact_fv_empty_0687 h)

theorem nb078_wpp_notmem_2308 : (nb078_alpha_dummy_889) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_889, fv_syn_cnnc] using (nb078_compact_fv_empty_0688)

theorem nb078_wpp_notmem_2309 (h : Var) : (nb078_alpha_dummy_891 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_891, fv_syn_cnnc] using (nb078_compact_fv_empty_0689 h)

theorem nb078_wpp_notmem_2310 : (nb078_alpha_dummy_895) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_895, fv_syn_cnnc] using (nb078_compact_fv_empty_0690)

theorem nb078_wpp_notmem_2311 (h : Var) : (nb078_alpha_dummy_896 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_896, fv_syn_cnnc] using (nb078_compact_fv_empty_0691 h)

theorem nb078_wpp_notmem_2312 : (nb078_alpha_dummy_893) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_893, fv_syn_cnnc] using (nb078_compact_fv_empty_0692)

theorem nb078_wpp_notmem_2313 (h : Var) : (nb078_alpha_dummy_894 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_894, fv_syn_cnnc] using (nb078_compact_fv_empty_0693 h)

theorem nb078_compact_envfresh_0360 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_901), (nb078_alpha_dummy_902 h)), ((nb078_alpha_dummy_897), (nb078_alpha_dummy_899 h)), ((nb078_alpha_dummy_898), (nb078_alpha_dummy_900 h)), ((nb078_alpha_dummy_890), (nb078_alpha_dummy_892 h)), ((nb078_alpha_dummy_889), (nb078_alpha_dummy_891 h)), ((nb078_alpha_dummy_895), (nb078_alpha_dummy_896 h)), ((nb078_alpha_dummy_893), (nb078_alpha_dummy_894 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_901) (nb078_alpha_dummy_902 h) (nb078_wpp_notmem_2300) (nb078_wpp_notmem_2301 h) (TEnvFresh.consFresh (nb078_alpha_dummy_897) (nb078_alpha_dummy_899 h) (nb078_wpp_notmem_2302) (nb078_wpp_notmem_2303 h) (TEnvFresh.consFresh (nb078_alpha_dummy_898) (nb078_alpha_dummy_900 h) (nb078_wpp_notmem_2304) (nb078_wpp_notmem_2305 h) (TEnvFresh.consFresh (nb078_alpha_dummy_890) (nb078_alpha_dummy_892 h) (nb078_wpp_notmem_2306) (nb078_wpp_notmem_2307 h) (TEnvFresh.consFresh (nb078_alpha_dummy_889) (nb078_alpha_dummy_891 h) (nb078_wpp_notmem_2308) (nb078_wpp_notmem_2309 h) (TEnvFresh.consFresh (nb078_alpha_dummy_895) (nb078_alpha_dummy_896 h) (nb078_wpp_notmem_2310) (nb078_wpp_notmem_2311 h) (TEnvFresh.consFresh (nb078_alpha_dummy_893) (nb078_alpha_dummy_894 h) (nb078_wpp_notmem_2312) (nb078_wpp_notmem_2313 h) (TEnvFresh.consFresh (nb078_alpha_dummy_848) (nb078_alpha_dummy_850 h) (nb078_wpp_notmem_2220) (nb078_wpp_notmem_2221 h) (TEnvFresh.consFresh (nb078_alpha_dummy_847) (nb078_alpha_dummy_849 h) (nb078_wpp_notmem_2222) (nb078_wpp_notmem_2223 h) (TEnvFresh.consFresh (nb078_alpha_dummy_851) (nb078_alpha_dummy_852 h) (nb078_wpp_notmem_2224) (nb078_wpp_notmem_2225 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2122) (nb078_wpp_notmem_2123 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_2012) (nb078_wpp_notmem_2013 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_2014) (nb078_wpp_notmem_2015 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_2016) (nb078_wpp_notmem_2017 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_2018) (nb078_wpp_notmem_2019 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_2020) (nb078_wpp_notmem_2021 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
