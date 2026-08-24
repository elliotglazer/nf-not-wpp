import NAR4C078C001Part127

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

theorem nb078_compact_envfresh_0349 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_823) (nb078_alpha_dummy_824 h) (nb078_wpp_notmem_2108) (nb078_wpp_notmem_2109 h) (TEnvFresh.consFresh (nb078_alpha_dummy_819) (nb078_alpha_dummy_821 h) (nb078_wpp_notmem_2110) (nb078_wpp_notmem_2111 h) (TEnvFresh.consFresh (nb078_alpha_dummy_820) (nb078_alpha_dummy_822 h) (nb078_wpp_notmem_2112) (nb078_wpp_notmem_2113 h) (TEnvFresh.consFresh (nb078_alpha_dummy_845) (nb078_alpha_dummy_846 h) (nb078_wpp_notmem_2136) (nb078_wpp_notmem_2137 h) (TEnvFresh.consFresh (nb078_alpha_dummy_843) (nb078_alpha_dummy_844 h) (nb078_wpp_notmem_2138) (nb078_wpp_notmem_2139 h) (TEnvFresh.consFresh (nb078_alpha_dummy_812) (nb078_alpha_dummy_814 h) (nb078_wpp_notmem_2114) (nb078_wpp_notmem_2115 h) (TEnvFresh.consFresh (nb078_alpha_dummy_811) (nb078_alpha_dummy_813 h) (nb078_wpp_notmem_2116) (nb078_wpp_notmem_2117 h) (TEnvFresh.consFresh (nb078_alpha_dummy_841) (nb078_alpha_dummy_842 h) (nb078_wpp_notmem_2140) (nb078_wpp_notmem_2141 h) (TEnvFresh.consFresh (nb078_alpha_dummy_815) (nb078_alpha_dummy_816 h) (nb078_wpp_notmem_2120) (nb078_wpp_notmem_2121 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2122) (nb078_wpp_notmem_2123 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_2012) (nb078_wpp_notmem_2013 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_2014) (nb078_wpp_notmem_2015 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_2016) (nb078_wpp_notmem_2017 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_2018) (nb078_wpp_notmem_2019 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_2020) (nb078_wpp_notmem_2021 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))

noncomputable def nb078_wpp_refl_0349 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0349 x y h)

noncomputable def nb078_split_alpha_0105 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.classMem (Class.cv (nb078_alpha_dummy_843)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_812))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_844 h)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0846) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0847 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0846) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0847 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0876) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0877 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0874) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0875 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_812))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_814 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0850) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0851 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0850) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0851 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0848) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0849 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826), (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)), ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0347 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0854) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0855 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0852) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0853 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0858) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0859 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0856) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0857 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0854) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0855 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0852) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0853 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0858) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0859 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0856) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0857 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826), (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)), ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0348 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0862) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0863 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0860) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0861 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0862) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0863 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0860) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0861 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0866) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0867 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0864) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0865 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0866) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0867 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0864) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0865 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0848) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0849 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0349 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0848) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0849 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0848) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0849 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0349 x y h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0846) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0847 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0846) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0847 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0876) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0877 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0874) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0875 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_812))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_814 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0850) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0851 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0850) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0851 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0848) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0849 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826), (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)), ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0347 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0854) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0855 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0852) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0853 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0858) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0859 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0856) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0857 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0854) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0855 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0852) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0853 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0858) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0859 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0856) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0857 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826), (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)), ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0348 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0862) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0863 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0860) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0861 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0862) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0863 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0860) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0861 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0866) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0867 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0864) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0865 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0866) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0867 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0864) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0865 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0848) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0849 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0349 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0848) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0849 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0848) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0849 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_845), (nb078_alpha_dummy_846 h)), ((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0349 x y h))))))))))))))))))))))))

theorem nb078_wpp_notmem_2142 : (nb078_alpha_dummy_843) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_843, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0638)

theorem nb078_wpp_notmem_2143 (h : Var) : (nb078_alpha_dummy_844 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_844, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0639 h)

theorem nb078_wpp_notmem_2144 : (nb078_alpha_dummy_812) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_812, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0626)

theorem nb078_wpp_notmem_2145 (h : Var) : (nb078_alpha_dummy_814 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_814, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0627 h)

theorem nb078_wpp_notmem_2146 : (nb078_alpha_dummy_811) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_811, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0628)

theorem nb078_wpp_notmem_2147 (h : Var) : (nb078_alpha_dummy_813 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_813, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0629 h)

theorem nb078_wpp_notmem_2148 : (nb078_alpha_dummy_841) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_841, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0640)

theorem nb078_wpp_notmem_2149 (h : Var) : (nb078_alpha_dummy_842 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_842, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0641 h)

theorem nb078_wpp_notmem_2150 : (nb078_alpha_dummy_815) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_815, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0632)

theorem nb078_wpp_notmem_2151 (h : Var) : (nb078_alpha_dummy_816 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_816, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0633 h)

theorem nb078_wpp_notmem_2152 : (nb078_alpha_dummy_769) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_769, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0634)

theorem nb078_wpp_notmem_2153 (h : Var) : (nb078_alpha_dummy_772 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_772, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0635 h)

theorem nb078_compact_envfresh_0350 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_843) (nb078_alpha_dummy_844 h) (nb078_wpp_notmem_2142) (nb078_wpp_notmem_2143 h) (TEnvFresh.consFresh (nb078_alpha_dummy_812) (nb078_alpha_dummy_814 h) (nb078_wpp_notmem_2144) (nb078_wpp_notmem_2145 h) (TEnvFresh.consFresh (nb078_alpha_dummy_811) (nb078_alpha_dummy_813 h) (nb078_wpp_notmem_2146) (nb078_wpp_notmem_2147 h) (TEnvFresh.consFresh (nb078_alpha_dummy_841) (nb078_alpha_dummy_842 h) (nb078_wpp_notmem_2148) (nb078_wpp_notmem_2149 h) (TEnvFresh.consFresh (nb078_alpha_dummy_815) (nb078_alpha_dummy_816 h) (nb078_wpp_notmem_2150) (nb078_wpp_notmem_2151 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2152) (nb078_wpp_notmem_2153 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_2052) (nb078_wpp_notmem_2053 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_2054) (nb078_wpp_notmem_2055 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_2056) (nb078_wpp_notmem_2057 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_2058) (nb078_wpp_notmem_2059 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_2060) (nb078_wpp_notmem_2061 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2062) (nb078_wpp_notmem_2063 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb078_wpp_refl_0350 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_843), (nb078_alpha_dummy_844 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_841), (nb078_alpha_dummy_842 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0350 x y h)

theorem nb078_compact_fv_empty_0642 : (nb078_alpha_dummy_869) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2154 : (nb078_alpha_dummy_869) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_869, fv_syn_c1c] using (nb078_compact_fv_empty_0642)

theorem nb078_compact_fv_empty_0643 (h : Var) : (nb078_alpha_dummy_872 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2155 (h : Var) : (nb078_alpha_dummy_872 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_872, fv_syn_c1c] using (nb078_compact_fv_empty_0643 h)

theorem nb078_compact_fv_empty_0644 : (nb078_alpha_dummy_868) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2156 : (nb078_alpha_dummy_868) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_868, fv_syn_c1c] using (nb078_compact_fv_empty_0644)

theorem nb078_compact_fv_empty_0645 (h : Var) : (nb078_alpha_dummy_871 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2157 (h : Var) : (nb078_alpha_dummy_871 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_871, fv_syn_c1c] using (nb078_compact_fv_empty_0645 h)

theorem nb078_compact_fv_empty_0646 : (nb078_alpha_dummy_867) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2158 : (nb078_alpha_dummy_867) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_867, fv_syn_c1c] using (nb078_compact_fv_empty_0646)

theorem nb078_compact_fv_empty_0647 (h : Var) : (nb078_alpha_dummy_870 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2159 (h : Var) : (nb078_alpha_dummy_870 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_870, fv_syn_c1c] using (nb078_compact_fv_empty_0647 h)

theorem nb078_compact_fv_empty_0648 : (nb078_alpha_dummy_865) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2160 : (nb078_alpha_dummy_865) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_865, fv_syn_c1c] using (nb078_compact_fv_empty_0648)

theorem nb078_compact_fv_empty_0649 (h : Var) : (nb078_alpha_dummy_866 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2161 (h : Var) : (nb078_alpha_dummy_866 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_866, fv_syn_c1c] using (nb078_compact_fv_empty_0649 h)

theorem nb078_compact_fv_empty_0650 : (nb078_alpha_dummy_861) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2162 : (nb078_alpha_dummy_861) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_861, fv_syn_c1c] using (nb078_compact_fv_empty_0650)

theorem nb078_compact_fv_empty_0651 (h : Var) : (nb078_alpha_dummy_863 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2163 (h : Var) : (nb078_alpha_dummy_863 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_863, fv_syn_c1c] using (nb078_compact_fv_empty_0651 h)

theorem nb078_compact_fv_empty_0652 : (nb078_alpha_dummy_862) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2164 : (nb078_alpha_dummy_862) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_862, fv_syn_c1c] using (nb078_compact_fv_empty_0652)

theorem nb078_compact_fv_empty_0653 (h : Var) : (nb078_alpha_dummy_864 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2165 (h : Var) : (nb078_alpha_dummy_864 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_864, fv_syn_c1c] using (nb078_compact_fv_empty_0653 h)

theorem nb078_compact_fv_empty_0654 : (nb078_alpha_dummy_854) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2166 : (nb078_alpha_dummy_854) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_854, fv_syn_c1c] using (nb078_compact_fv_empty_0654)

theorem nb078_compact_fv_empty_0655 (h : Var) : (nb078_alpha_dummy_856 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2167 (h : Var) : (nb078_alpha_dummy_856 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_856, fv_syn_c1c] using (nb078_compact_fv_empty_0655 h)

theorem nb078_compact_fv_empty_0656 : (nb078_alpha_dummy_853) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2168 : (nb078_alpha_dummy_853) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_853, fv_syn_c1c] using (nb078_compact_fv_empty_0656)

theorem nb078_compact_fv_empty_0657 (h : Var) : (nb078_alpha_dummy_855 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2169 (h : Var) : (nb078_alpha_dummy_855 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_855, fv_syn_c1c] using (nb078_compact_fv_empty_0657 h)

theorem nb078_compact_fv_empty_0658 : (nb078_alpha_dummy_859) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2170 : (nb078_alpha_dummy_859) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_859, fv_syn_c1c] using (nb078_compact_fv_empty_0658)

theorem nb078_compact_fv_empty_0659 (h : Var) : (nb078_alpha_dummy_860 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2171 (h : Var) : (nb078_alpha_dummy_860 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_860, fv_syn_c1c] using (nb078_compact_fv_empty_0659 h)

theorem nb078_compact_fv_empty_0660 : (nb078_alpha_dummy_857) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2172 : (nb078_alpha_dummy_857) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_857, fv_syn_c1c] using (nb078_compact_fv_empty_0660)

theorem nb078_compact_fv_empty_0661 (h : Var) : (nb078_alpha_dummy_858 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2173 (h : Var) : (nb078_alpha_dummy_858 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_858, fv_syn_c1c] using (nb078_compact_fv_empty_0661 h)

theorem nb078_compact_fv_empty_0662 : (nb078_alpha_dummy_848) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2174 : (nb078_alpha_dummy_848) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_848, fv_syn_c1c] using (nb078_compact_fv_empty_0662)

theorem nb078_compact_fv_empty_0663 (h : Var) : (nb078_alpha_dummy_850 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2175 (h : Var) : (nb078_alpha_dummy_850 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_850, fv_syn_c1c] using (nb078_compact_fv_empty_0663 h)

theorem nb078_compact_fv_empty_0664 : (nb078_alpha_dummy_847) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2176 : (nb078_alpha_dummy_847) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_847, fv_syn_c1c] using (nb078_compact_fv_empty_0664)

theorem nb078_compact_fv_empty_0665 (h : Var) : (nb078_alpha_dummy_849 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2177 (h : Var) : (nb078_alpha_dummy_849 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_849, fv_syn_c1c] using (nb078_compact_fv_empty_0665 h)

theorem nb078_compact_fv_empty_0666 : (nb078_alpha_dummy_851) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2178 : (nb078_alpha_dummy_851) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_851, fv_syn_c1c] using (nb078_compact_fv_empty_0666)

theorem nb078_compact_fv_empty_0667 (h : Var) : (nb078_alpha_dummy_852 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2179 (h : Var) : (nb078_alpha_dummy_852 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_852, fv_syn_c1c] using (nb078_compact_fv_empty_0667 h)

theorem nb078_compact_envfresh_0351 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_869) (nb078_alpha_dummy_872 h) (nb078_wpp_notmem_2154) (nb078_wpp_notmem_2155 h) (TEnvFresh.consFresh (nb078_alpha_dummy_868) (nb078_alpha_dummy_871 h) (nb078_wpp_notmem_2156) (nb078_wpp_notmem_2157 h) (TEnvFresh.consFresh (nb078_alpha_dummy_867) (nb078_alpha_dummy_870 h) (nb078_wpp_notmem_2158) (nb078_wpp_notmem_2159 h) (TEnvFresh.consFresh (nb078_alpha_dummy_865) (nb078_alpha_dummy_866 h) (nb078_wpp_notmem_2160) (nb078_wpp_notmem_2161 h) (TEnvFresh.consFresh (nb078_alpha_dummy_861) (nb078_alpha_dummy_863 h) (nb078_wpp_notmem_2162) (nb078_wpp_notmem_2163 h) (TEnvFresh.consFresh (nb078_alpha_dummy_862) (nb078_alpha_dummy_864 h) (nb078_wpp_notmem_2164) (nb078_wpp_notmem_2165 h) (TEnvFresh.consFresh (nb078_alpha_dummy_854) (nb078_alpha_dummy_856 h) (nb078_wpp_notmem_2166) (nb078_wpp_notmem_2167 h) (TEnvFresh.consFresh (nb078_alpha_dummy_853) (nb078_alpha_dummy_855 h) (nb078_wpp_notmem_2168) (nb078_wpp_notmem_2169 h) (TEnvFresh.consFresh (nb078_alpha_dummy_859) (nb078_alpha_dummy_860 h) (nb078_wpp_notmem_2170) (nb078_wpp_notmem_2171 h) (TEnvFresh.consFresh (nb078_alpha_dummy_857) (nb078_alpha_dummy_858 h) (nb078_wpp_notmem_2172) (nb078_wpp_notmem_2173 h) (TEnvFresh.consFresh (nb078_alpha_dummy_848) (nb078_alpha_dummy_850 h) (nb078_wpp_notmem_2174) (nb078_wpp_notmem_2175 h) (TEnvFresh.consFresh (nb078_alpha_dummy_847) (nb078_alpha_dummy_849 h) (nb078_wpp_notmem_2176) (nb078_wpp_notmem_2177 h) (TEnvFresh.consFresh (nb078_alpha_dummy_851) (nb078_alpha_dummy_852 h) (nb078_wpp_notmem_2178) (nb078_wpp_notmem_2179 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2084) (nb078_wpp_notmem_2085 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1954) (nb078_wpp_notmem_1955 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1956) (nb078_wpp_notmem_1957 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1958) (nb078_wpp_notmem_1959 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1960) (nb078_wpp_notmem_1961 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1962) (nb078_wpp_notmem_1963 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0351 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0351 x y h)

theorem nb078_wpp_notmem_2180 : (nb078_alpha_dummy_869) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_869, fv_syn_c0] using (nb078_compact_fv_empty_0642)

theorem nb078_wpp_notmem_2181 (h : Var) : (nb078_alpha_dummy_872 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_872, fv_syn_c0] using (nb078_compact_fv_empty_0643 h)

theorem nb078_wpp_notmem_2182 : (nb078_alpha_dummy_868) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_868, fv_syn_c0] using (nb078_compact_fv_empty_0644)

theorem nb078_wpp_notmem_2183 (h : Var) : (nb078_alpha_dummy_871 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_871, fv_syn_c0] using (nb078_compact_fv_empty_0645 h)

theorem nb078_wpp_notmem_2184 : (nb078_alpha_dummy_867) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_867, fv_syn_c0] using (nb078_compact_fv_empty_0646)

theorem nb078_wpp_notmem_2185 (h : Var) : (nb078_alpha_dummy_870 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_870, fv_syn_c0] using (nb078_compact_fv_empty_0647 h)

theorem nb078_wpp_notmem_2186 : (nb078_alpha_dummy_865) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_865, fv_syn_c0] using (nb078_compact_fv_empty_0648)

theorem nb078_wpp_notmem_2187 (h : Var) : (nb078_alpha_dummy_866 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_866, fv_syn_c0] using (nb078_compact_fv_empty_0649 h)

theorem nb078_wpp_notmem_2188 : (nb078_alpha_dummy_861) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_861, fv_syn_c0] using (nb078_compact_fv_empty_0650)

theorem nb078_wpp_notmem_2189 (h : Var) : (nb078_alpha_dummy_863 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_863, fv_syn_c0] using (nb078_compact_fv_empty_0651 h)

theorem nb078_wpp_notmem_2190 : (nb078_alpha_dummy_862) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_862, fv_syn_c0] using (nb078_compact_fv_empty_0652)

theorem nb078_wpp_notmem_2191 (h : Var) : (nb078_alpha_dummy_864 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_864, fv_syn_c0] using (nb078_compact_fv_empty_0653 h)

theorem nb078_wpp_notmem_2192 : (nb078_alpha_dummy_854) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_854, fv_syn_c0] using (nb078_compact_fv_empty_0654)

theorem nb078_wpp_notmem_2193 (h : Var) : (nb078_alpha_dummy_856 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_856, fv_syn_c0] using (nb078_compact_fv_empty_0655 h)

theorem nb078_wpp_notmem_2194 : (nb078_alpha_dummy_853) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_853, fv_syn_c0] using (nb078_compact_fv_empty_0656)

theorem nb078_wpp_notmem_2195 (h : Var) : (nb078_alpha_dummy_855 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_855, fv_syn_c0] using (nb078_compact_fv_empty_0657 h)

theorem nb078_wpp_notmem_2196 : (nb078_alpha_dummy_859) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_859, fv_syn_c0] using (nb078_compact_fv_empty_0658)

theorem nb078_wpp_notmem_2197 (h : Var) : (nb078_alpha_dummy_860 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_860, fv_syn_c0] using (nb078_compact_fv_empty_0659 h)

theorem nb078_wpp_notmem_2198 : (nb078_alpha_dummy_857) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_857, fv_syn_c0] using (nb078_compact_fv_empty_0660)

theorem nb078_wpp_notmem_2199 (h : Var) : (nb078_alpha_dummy_858 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_858, fv_syn_c0] using (nb078_compact_fv_empty_0661 h)

theorem nb078_wpp_notmem_2200 : (nb078_alpha_dummy_848) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_848, fv_syn_c0] using (nb078_compact_fv_empty_0662)

theorem nb078_wpp_notmem_2201 (h : Var) : (nb078_alpha_dummy_850 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_850, fv_syn_c0] using (nb078_compact_fv_empty_0663 h)

theorem nb078_wpp_notmem_2202 : (nb078_alpha_dummy_847) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_847, fv_syn_c0] using (nb078_compact_fv_empty_0664)

theorem nb078_wpp_notmem_2203 (h : Var) : (nb078_alpha_dummy_849 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_849, fv_syn_c0] using (nb078_compact_fv_empty_0665 h)

theorem nb078_wpp_notmem_2204 : (nb078_alpha_dummy_851) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_851, fv_syn_c0] using (nb078_compact_fv_empty_0666)

theorem nb078_wpp_notmem_2205 (h : Var) : (nb078_alpha_dummy_852 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_852, fv_syn_c0] using (nb078_compact_fv_empty_0667 h)

theorem nb078_compact_envfresh_0352 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_869) (nb078_alpha_dummy_872 h) (nb078_wpp_notmem_2180) (nb078_wpp_notmem_2181 h) (TEnvFresh.consFresh (nb078_alpha_dummy_868) (nb078_alpha_dummy_871 h) (nb078_wpp_notmem_2182) (nb078_wpp_notmem_2183 h) (TEnvFresh.consFresh (nb078_alpha_dummy_867) (nb078_alpha_dummy_870 h) (nb078_wpp_notmem_2184) (nb078_wpp_notmem_2185 h) (TEnvFresh.consFresh (nb078_alpha_dummy_865) (nb078_alpha_dummy_866 h) (nb078_wpp_notmem_2186) (nb078_wpp_notmem_2187 h) (TEnvFresh.consFresh (nb078_alpha_dummy_861) (nb078_alpha_dummy_863 h) (nb078_wpp_notmem_2188) (nb078_wpp_notmem_2189 h) (TEnvFresh.consFresh (nb078_alpha_dummy_862) (nb078_alpha_dummy_864 h) (nb078_wpp_notmem_2190) (nb078_wpp_notmem_2191 h) (TEnvFresh.consFresh (nb078_alpha_dummy_854) (nb078_alpha_dummy_856 h) (nb078_wpp_notmem_2192) (nb078_wpp_notmem_2193 h) (TEnvFresh.consFresh (nb078_alpha_dummy_853) (nb078_alpha_dummy_855 h) (nb078_wpp_notmem_2194) (nb078_wpp_notmem_2195 h) (TEnvFresh.consFresh (nb078_alpha_dummy_859) (nb078_alpha_dummy_860 h) (nb078_wpp_notmem_2196) (nb078_wpp_notmem_2197 h) (TEnvFresh.consFresh (nb078_alpha_dummy_857) (nb078_alpha_dummy_858 h) (nb078_wpp_notmem_2198) (nb078_wpp_notmem_2199 h) (TEnvFresh.consFresh (nb078_alpha_dummy_848) (nb078_alpha_dummy_850 h) (nb078_wpp_notmem_2200) (nb078_wpp_notmem_2201 h) (TEnvFresh.consFresh (nb078_alpha_dummy_847) (nb078_alpha_dummy_849 h) (nb078_wpp_notmem_2202) (nb078_wpp_notmem_2203 h) (TEnvFresh.consFresh (nb078_alpha_dummy_851) (nb078_alpha_dummy_852 h) (nb078_wpp_notmem_2204) (nb078_wpp_notmem_2205 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2106) (nb078_wpp_notmem_2107 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1986) (nb078_wpp_notmem_1987 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1988) (nb078_wpp_notmem_1989 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1990) (nb078_wpp_notmem_1991 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1992) (nb078_wpp_notmem_1993 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1994) (nb078_wpp_notmem_1995 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0352 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_869), (nb078_alpha_dummy_872 h)), ((nb078_alpha_dummy_868), (nb078_alpha_dummy_871 h)), ((nb078_alpha_dummy_867), (nb078_alpha_dummy_870 h)), ((nb078_alpha_dummy_865), (nb078_alpha_dummy_866 h)), ((nb078_alpha_dummy_861), (nb078_alpha_dummy_863 h)), ((nb078_alpha_dummy_862), (nb078_alpha_dummy_864 h)), ((nb078_alpha_dummy_854), (nb078_alpha_dummy_856 h)), ((nb078_alpha_dummy_853), (nb078_alpha_dummy_855 h)), ((nb078_alpha_dummy_859), (nb078_alpha_dummy_860 h)), ((nb078_alpha_dummy_857), (nb078_alpha_dummy_858 h)), ((nb078_alpha_dummy_848), (nb078_alpha_dummy_850 h)), ((nb078_alpha_dummy_847), (nb078_alpha_dummy_849 h)), ((nb078_alpha_dummy_851), (nb078_alpha_dummy_852 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0352 x y h)

theorem nb078_wpp_notmem_2206 : (nb078_alpha_dummy_865) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_865, fv_syn_cnnc] using (nb078_compact_fv_empty_0648)

theorem nb078_wpp_notmem_2207 (h : Var) : (nb078_alpha_dummy_866 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_866, fv_syn_cnnc] using (nb078_compact_fv_empty_0649 h)

theorem nb078_wpp_notmem_2208 : (nb078_alpha_dummy_861) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_861, fv_syn_cnnc] using (nb078_compact_fv_empty_0650)

theorem nb078_wpp_notmem_2209 (h : Var) : (nb078_alpha_dummy_863 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_863, fv_syn_cnnc] using (nb078_compact_fv_empty_0651 h)

theorem nb078_wpp_notmem_2210 : (nb078_alpha_dummy_862) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_862, fv_syn_cnnc] using (nb078_compact_fv_empty_0652)

theorem nb078_wpp_notmem_2211 (h : Var) : (nb078_alpha_dummy_864 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_864, fv_syn_cnnc] using (nb078_compact_fv_empty_0653 h)

theorem nb078_wpp_notmem_2212 : (nb078_alpha_dummy_854) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_854, fv_syn_cnnc] using (nb078_compact_fv_empty_0654)

theorem nb078_wpp_notmem_2213 (h : Var) : (nb078_alpha_dummy_856 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_856, fv_syn_cnnc] using (nb078_compact_fv_empty_0655 h)

theorem nb078_wpp_notmem_2214 : (nb078_alpha_dummy_853) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_853, fv_syn_cnnc] using (nb078_compact_fv_empty_0656)

theorem nb078_wpp_notmem_2215 (h : Var) : (nb078_alpha_dummy_855 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_855, fv_syn_cnnc] using (nb078_compact_fv_empty_0657 h)

theorem nb078_wpp_notmem_2216 : (nb078_alpha_dummy_859) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_859, fv_syn_cnnc] using (nb078_compact_fv_empty_0658)

theorem nb078_wpp_notmem_2217 (h : Var) : (nb078_alpha_dummy_860 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_860, fv_syn_cnnc] using (nb078_compact_fv_empty_0659 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
