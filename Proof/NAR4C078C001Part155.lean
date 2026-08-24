import NAR4C078C001Part154

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

noncomputable def nb078_wpp_refl_0449 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0449 x y h)

theorem nb078_wpp_notmem_2746 : (nb078_alpha_dummy_1091) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0820)

theorem nb078_wpp_notmem_2747 (h : Var) : (nb078_alpha_dummy_1092 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0821 h)

theorem nb078_wpp_notmem_2748 : (nb078_alpha_dummy_1089) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0822)

theorem nb078_wpp_notmem_2749 (h : Var) : (nb078_alpha_dummy_1090 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0823 h)

theorem nb078_wpp_notmem_2750 : (nb078_alpha_dummy_1087) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0824)

theorem nb078_wpp_notmem_2751 (h : Var) : (nb078_alpha_dummy_1088 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0825 h)

theorem nb078_compact_envfresh_0450 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1073) (nb078_alpha_dummy_1076 h) (nb078_wpp_notmem_2686) (nb078_wpp_notmem_2687 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1072) (nb078_alpha_dummy_1075 h) (nb078_wpp_notmem_2688) (nb078_wpp_notmem_2689 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1071) (nb078_alpha_dummy_1074 h) (nb078_wpp_notmem_2690) (nb078_wpp_notmem_2691 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1069) (nb078_alpha_dummy_1070 h) (nb078_wpp_notmem_2692) (nb078_wpp_notmem_2693 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1065) (nb078_alpha_dummy_1067 h) (nb078_wpp_notmem_2694) (nb078_wpp_notmem_2695 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1066) (nb078_alpha_dummy_1068 h) (nb078_wpp_notmem_2696) (nb078_wpp_notmem_2697 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1091) (nb078_alpha_dummy_1092 h) (nb078_wpp_notmem_2746) (nb078_wpp_notmem_2747 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1089) (nb078_alpha_dummy_1090 h) (nb078_wpp_notmem_2748) (nb078_wpp_notmem_2749 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1058) (nb078_alpha_dummy_1060 h) (nb078_wpp_notmem_2698) (nb078_wpp_notmem_2699 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1057) (nb078_alpha_dummy_1059 h) (nb078_wpp_notmem_2700) (nb078_wpp_notmem_2701 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1087) (nb078_alpha_dummy_1088 h) (nb078_wpp_notmem_2750) (nb078_wpp_notmem_2751 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1061) (nb078_alpha_dummy_1062 h) (nb078_wpp_notmem_2704) (nb078_wpp_notmem_2705 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2706) (nb078_wpp_notmem_2707 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2708) (nb078_wpp_notmem_2709 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2710) (nb078_wpp_notmem_2711 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2712) (nb078_wpp_notmem_2713 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2714) (nb078_wpp_notmem_2715 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb078_wpp_refl_0450 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0450 x y h)

theorem nb078_wpp_notmem_2752 : (nb078_alpha_dummy_1091) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0820)

theorem nb078_wpp_notmem_2753 (h : Var) : (nb078_alpha_dummy_1092 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0821 h)

theorem nb078_wpp_notmem_2754 : (nb078_alpha_dummy_1089) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0822)

theorem nb078_wpp_notmem_2755 (h : Var) : (nb078_alpha_dummy_1090 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0823 h)

theorem nb078_wpp_notmem_2756 : (nb078_alpha_dummy_1087) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0824)

theorem nb078_wpp_notmem_2757 (h : Var) : (nb078_alpha_dummy_1088 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0825 h)

theorem nb078_compact_envfresh_0451 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1069) (nb078_alpha_dummy_1070 h) (nb078_wpp_notmem_2716) (nb078_wpp_notmem_2717 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1065) (nb078_alpha_dummy_1067 h) (nb078_wpp_notmem_2718) (nb078_wpp_notmem_2719 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1066) (nb078_alpha_dummy_1068 h) (nb078_wpp_notmem_2720) (nb078_wpp_notmem_2721 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1091) (nb078_alpha_dummy_1092 h) (nb078_wpp_notmem_2752) (nb078_wpp_notmem_2753 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1089) (nb078_alpha_dummy_1090 h) (nb078_wpp_notmem_2754) (nb078_wpp_notmem_2755 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1058) (nb078_alpha_dummy_1060 h) (nb078_wpp_notmem_2722) (nb078_wpp_notmem_2723 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1057) (nb078_alpha_dummy_1059 h) (nb078_wpp_notmem_2724) (nb078_wpp_notmem_2725 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1087) (nb078_alpha_dummy_1088 h) (nb078_wpp_notmem_2756) (nb078_wpp_notmem_2757 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1061) (nb078_alpha_dummy_1062 h) (nb078_wpp_notmem_2728) (nb078_wpp_notmem_2729 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2730) (nb078_wpp_notmem_2731 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2732) (nb078_wpp_notmem_2733 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2734) (nb078_wpp_notmem_2735 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2736) (nb078_wpp_notmem_2737 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2738) (nb078_wpp_notmem_2739 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0451 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0451 x y h)

theorem nb078_wpp_notmem_2758 : (nb078_alpha_dummy_1089) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0822)

theorem nb078_wpp_notmem_2759 (h : Var) : (nb078_alpha_dummy_1090 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0823 h)

theorem nb078_wpp_notmem_2760 : (nb078_alpha_dummy_1058) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0802)

theorem nb078_wpp_notmem_2761 (h : Var) : (nb078_alpha_dummy_1060 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0803 h)

theorem nb078_wpp_notmem_2762 : (nb078_alpha_dummy_1057) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0804)

theorem nb078_wpp_notmem_2763 (h : Var) : (nb078_alpha_dummy_1059 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0805 h)

theorem nb078_wpp_notmem_2764 : (nb078_alpha_dummy_1087) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0824)

theorem nb078_wpp_notmem_2765 (h : Var) : (nb078_alpha_dummy_1088 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0825 h)

theorem nb078_wpp_notmem_2766 : (nb078_alpha_dummy_1061) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0808)

theorem nb078_wpp_notmem_2767 (h : Var) : (nb078_alpha_dummy_1062 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0809 h)

theorem nb078_wpp_notmem_2768 : (nb078_alpha_dummy_1050) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0810)

theorem nb078_wpp_notmem_2769 (h : Var) : (nb078_alpha_dummy_1053 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0811 h)

theorem nb078_wpp_notmem_2770 : (nb078_alpha_dummy_1049) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0812)

theorem nb078_wpp_notmem_2771 (h : Var) : (nb078_alpha_dummy_1052 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0813 h)

theorem nb078_wpp_notmem_2772 : (nb078_alpha_dummy_1055) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0814)

theorem nb078_wpp_notmem_2773 (h : Var) : (nb078_alpha_dummy_1056 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0815 h)

theorem nb078_wpp_notmem_2774 : (nb078_alpha_dummy_1047) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0816)

theorem nb078_wpp_notmem_2775 (h : Var) : (nb078_alpha_dummy_1048 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0817 h)

theorem nb078_wpp_notmem_2776 : (nb078_alpha_dummy_1045) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0818)

theorem nb078_wpp_notmem_2777 (h : Var) : (nb078_alpha_dummy_1046 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0819 h)

theorem nb078_compact_envfresh_0452 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1089) (nb078_alpha_dummy_1090 h) (nb078_wpp_notmem_2758) (nb078_wpp_notmem_2759 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1058) (nb078_alpha_dummy_1060 h) (nb078_wpp_notmem_2760) (nb078_wpp_notmem_2761 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1057) (nb078_alpha_dummy_1059 h) (nb078_wpp_notmem_2762) (nb078_wpp_notmem_2763 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1087) (nb078_alpha_dummy_1088 h) (nb078_wpp_notmem_2764) (nb078_wpp_notmem_2765 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1061) (nb078_alpha_dummy_1062 h) (nb078_wpp_notmem_2766) (nb078_wpp_notmem_2767 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2768) (nb078_wpp_notmem_2769 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2770) (nb078_wpp_notmem_2771 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2772) (nb078_wpp_notmem_2773 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2774) (nb078_wpp_notmem_2775 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2776) (nb078_wpp_notmem_2777 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2062) (nb078_wpp_notmem_2063 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))

noncomputable def nb078_wpp_refl_0452 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0452 x y h)

noncomputable def nb078_split_alpha_0135 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1089)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1089)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1090 h)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1090 h)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1107 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1106) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1107 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1137 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1135 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1060 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1110) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1111 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1111 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0449 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1115 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1113 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1119 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1117 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1115 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1113 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1119 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1117 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0450 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1123 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1121 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1123 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1121 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1127 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1125 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1127 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1125 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0451 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0451 x y h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1107 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1106) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1107 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1136) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1137 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1134) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1135 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1060 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1110) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1111 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1111 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0449 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1115 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1113 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1119 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1117 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1115 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1113 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1119 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1117 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0450 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1123 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1121 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1123 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1121 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1127 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1125 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1127 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1125 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0451 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0451 x y h)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (nb078_wpp_refl_0452 x y h)))))

theorem nb078_compact_fv_empty_0826 : (nb078_alpha_dummy_1109) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2778 : (nb078_alpha_dummy_1109) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0826)

theorem nb078_compact_fv_empty_0827 (h : Var) : (nb078_alpha_dummy_1112 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2779 (h : Var) : (nb078_alpha_dummy_1112 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0827 h)

theorem nb078_compact_fv_empty_0828 : (nb078_alpha_dummy_1108) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2780 : (nb078_alpha_dummy_1108) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0828)

theorem nb078_compact_fv_empty_0829 (h : Var) : (nb078_alpha_dummy_1111 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2781 (h : Var) : (nb078_alpha_dummy_1111 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0829 h)

theorem nb078_compact_fv_empty_0830 : (nb078_alpha_dummy_1107) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2782 : (nb078_alpha_dummy_1107) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0830)

theorem nb078_compact_fv_empty_0831 (h : Var) : (nb078_alpha_dummy_1110 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2783 (h : Var) : (nb078_alpha_dummy_1110 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0831 h)

theorem nb078_compact_fv_empty_0832 : (nb078_alpha_dummy_1105) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2784 : (nb078_alpha_dummy_1105) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0832)

theorem nb078_compact_fv_empty_0833 (h : Var) : (nb078_alpha_dummy_1106 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2785 (h : Var) : (nb078_alpha_dummy_1106 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0833 h)

theorem nb078_compact_fv_empty_0834 : (nb078_alpha_dummy_1101) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2786 : (nb078_alpha_dummy_1101) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0834)

theorem nb078_compact_fv_empty_0835 (h : Var) : (nb078_alpha_dummy_1103 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2787 (h : Var) : (nb078_alpha_dummy_1103 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0835 h)

theorem nb078_compact_fv_empty_0836 : (nb078_alpha_dummy_1102) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2788 : (nb078_alpha_dummy_1102) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0836)

theorem nb078_compact_fv_empty_0837 (h : Var) : (nb078_alpha_dummy_1104 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2789 (h : Var) : (nb078_alpha_dummy_1104 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0837 h)

theorem nb078_compact_fv_empty_0838 : (nb078_alpha_dummy_1094) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2790 : (nb078_alpha_dummy_1094) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0838)

theorem nb078_compact_fv_empty_0839 (h : Var) : (nb078_alpha_dummy_1096 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2791 (h : Var) : (nb078_alpha_dummy_1096 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0839 h)

theorem nb078_compact_fv_empty_0840 : (nb078_alpha_dummy_1093) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2792 : (nb078_alpha_dummy_1093) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0840)

theorem nb078_compact_fv_empty_0841 (h : Var) : (nb078_alpha_dummy_1095 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2793 (h : Var) : (nb078_alpha_dummy_1095 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0841 h)

theorem nb078_compact_fv_empty_0842 : (nb078_alpha_dummy_1099) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2794 : (nb078_alpha_dummy_1099) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0842)

theorem nb078_compact_fv_empty_0843 (h : Var) : (nb078_alpha_dummy_1100 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2795 (h : Var) : (nb078_alpha_dummy_1100 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0843 h)

theorem nb078_compact_fv_empty_0844 : (nb078_alpha_dummy_1097) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2796 : (nb078_alpha_dummy_1097) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0844)

theorem nb078_compact_fv_empty_0845 (h : Var) : (nb078_alpha_dummy_1098 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2797 (h : Var) : (nb078_alpha_dummy_1098 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0845 h)

theorem nb078_compact_fv_empty_0846 : (nb078_alpha_dummy_1051) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2798 : (nb078_alpha_dummy_1051) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0846)

theorem nb078_compact_fv_empty_0847 (h : Var) : (nb078_alpha_dummy_1054 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2799 (h : Var) : (nb078_alpha_dummy_1054 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0847 h)

theorem nb078_compact_envfresh_0453 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108), (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)), ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1109) (nb078_alpha_dummy_1112 h) (nb078_wpp_notmem_2778) (nb078_wpp_notmem_2779 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1108) (nb078_alpha_dummy_1111 h) (nb078_wpp_notmem_2780) (nb078_wpp_notmem_2781 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1107) (nb078_alpha_dummy_1110 h) (nb078_wpp_notmem_2782) (nb078_wpp_notmem_2783 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1105) (nb078_alpha_dummy_1106 h) (nb078_wpp_notmem_2784) (nb078_wpp_notmem_2785 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1101) (nb078_alpha_dummy_1103 h) (nb078_wpp_notmem_2786) (nb078_wpp_notmem_2787 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1102) (nb078_alpha_dummy_1104 h) (nb078_wpp_notmem_2788) (nb078_wpp_notmem_2789 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1094) (nb078_alpha_dummy_1096 h) (nb078_wpp_notmem_2790) (nb078_wpp_notmem_2791 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1093) (nb078_alpha_dummy_1095 h) (nb078_wpp_notmem_2792) (nb078_wpp_notmem_2793 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1099) (nb078_alpha_dummy_1100 h) (nb078_wpp_notmem_2794) (nb078_wpp_notmem_2795 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1097) (nb078_alpha_dummy_1098 h) (nb078_wpp_notmem_2796) (nb078_wpp_notmem_2797 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1051) (nb078_alpha_dummy_1054 h) (nb078_wpp_notmem_2798) (nb078_wpp_notmem_2799 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2676) (nb078_wpp_notmem_2677 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2678) (nb078_wpp_notmem_2679 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2680) (nb078_wpp_notmem_2681 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2682) (nb078_wpp_notmem_2683 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2684) (nb078_wpp_notmem_2685 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0453 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1109), (nb078_alpha_dummy_1112 h)), ((nb078_alpha_dummy_1108), (nb078_alpha_dummy_1111 h)), ((nb078_alpha_dummy_1107), (nb078_alpha_dummy_1110 h)), ((nb078_alpha_dummy_1105), (nb078_alpha_dummy_1106 h)), ((nb078_alpha_dummy_1101), (nb078_alpha_dummy_1103 h)), ((nb078_alpha_dummy_1102), (nb078_alpha_dummy_1104 h)), ((nb078_alpha_dummy_1094), (nb078_alpha_dummy_1096 h)), ((nb078_alpha_dummy_1093), (nb078_alpha_dummy_1095 h)), ((nb078_alpha_dummy_1099), (nb078_alpha_dummy_1100 h)), ((nb078_alpha_dummy_1097), (nb078_alpha_dummy_1098 h)), ((nb078_alpha_dummy_1051), (nb078_alpha_dummy_1054 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0453 x y h)

theorem nb078_wpp_notmem_2800 : (nb078_alpha_dummy_1109) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0826)

theorem nb078_wpp_notmem_2801 (h : Var) : (nb078_alpha_dummy_1112 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0827 h)

theorem nb078_wpp_notmem_2802 : (nb078_alpha_dummy_1108) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0828)

theorem nb078_wpp_notmem_2803 (h : Var) : (nb078_alpha_dummy_1111 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0829 h)

theorem nb078_wpp_notmem_2804 : (nb078_alpha_dummy_1107) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0830)

theorem nb078_wpp_notmem_2805 (h : Var) : (nb078_alpha_dummy_1110 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0831 h)

theorem nb078_wpp_notmem_2806 : (nb078_alpha_dummy_1105) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0832)

theorem nb078_wpp_notmem_2807 (h : Var) : (nb078_alpha_dummy_1106 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0833 h)

theorem nb078_wpp_notmem_2808 : (nb078_alpha_dummy_1101) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0834)

theorem nb078_wpp_notmem_2809 (h : Var) : (nb078_alpha_dummy_1103 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0835 h)

theorem nb078_wpp_notmem_2810 : (nb078_alpha_dummy_1102) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0836)

theorem nb078_wpp_notmem_2811 (h : Var) : (nb078_alpha_dummy_1104 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0837 h)

theorem nb078_wpp_notmem_2812 : (nb078_alpha_dummy_1094) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0838)

theorem nb078_wpp_notmem_2813 (h : Var) : (nb078_alpha_dummy_1096 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0839 h)

theorem nb078_wpp_notmem_2814 : (nb078_alpha_dummy_1093) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0840)

theorem nb078_wpp_notmem_2815 (h : Var) : (nb078_alpha_dummy_1095 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0841 h)

theorem nb078_wpp_notmem_2816 : (nb078_alpha_dummy_1099) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0842)

theorem nb078_wpp_notmem_2817 (h : Var) : (nb078_alpha_dummy_1100 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0843 h)

theorem nb078_wpp_notmem_2818 : (nb078_alpha_dummy_1097) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0844)

theorem nb078_wpp_notmem_2819 (h : Var) : (nb078_alpha_dummy_1098 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0845 h)

theorem nb078_wpp_notmem_2820 : (nb078_alpha_dummy_1051) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0846)

theorem nb078_wpp_notmem_2821 (h : Var) : (nb078_alpha_dummy_1054 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0847 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
