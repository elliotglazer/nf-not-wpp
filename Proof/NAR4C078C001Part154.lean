import NAR4C078C001Part153

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

theorem nb078_wpp_notmem_2662 : (nb078_alpha_dummy_1069) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0796)

theorem nb078_compact_fv_empty_0797 (h : Var) : (nb078_alpha_dummy_1070 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2663 (h : Var) : (nb078_alpha_dummy_1070 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0797 h)

theorem nb078_compact_fv_empty_0798 : (nb078_alpha_dummy_1065) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2664 : (nb078_alpha_dummy_1065) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0798)

theorem nb078_compact_fv_empty_0799 (h : Var) : (nb078_alpha_dummy_1067 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2665 (h : Var) : (nb078_alpha_dummy_1067 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0799 h)

theorem nb078_compact_fv_empty_0800 : (nb078_alpha_dummy_1066) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2666 : (nb078_alpha_dummy_1066) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0800)

theorem nb078_compact_fv_empty_0801 (h : Var) : (nb078_alpha_dummy_1068 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2667 (h : Var) : (nb078_alpha_dummy_1068 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0801 h)

theorem nb078_compact_fv_empty_0802 : (nb078_alpha_dummy_1058) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2668 : (nb078_alpha_dummy_1058) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0802)

theorem nb078_compact_fv_empty_0803 (h : Var) : (nb078_alpha_dummy_1060 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2669 (h : Var) : (nb078_alpha_dummy_1060 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0803 h)

theorem nb078_compact_fv_empty_0804 : (nb078_alpha_dummy_1057) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2670 : (nb078_alpha_dummy_1057) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0804)

theorem nb078_compact_fv_empty_0805 (h : Var) : (nb078_alpha_dummy_1059 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2671 (h : Var) : (nb078_alpha_dummy_1059 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0805 h)

theorem nb078_compact_fv_empty_0806 : (nb078_alpha_dummy_1063) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2672 : (nb078_alpha_dummy_1063) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0806)

theorem nb078_compact_fv_empty_0807 (h : Var) : (nb078_alpha_dummy_1064 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2673 (h : Var) : (nb078_alpha_dummy_1064 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0807 h)

theorem nb078_compact_fv_empty_0808 : (nb078_alpha_dummy_1061) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2674 : (nb078_alpha_dummy_1061) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0808)

theorem nb078_compact_fv_empty_0809 (h : Var) : (nb078_alpha_dummy_1062 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2675 (h : Var) : (nb078_alpha_dummy_1062 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0809 h)

theorem nb078_compact_fv_empty_0810 : (nb078_alpha_dummy_1050) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2676 : (nb078_alpha_dummy_1050) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0810)

theorem nb078_compact_fv_empty_0811 (h : Var) : (nb078_alpha_dummy_1053 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2677 (h : Var) : (nb078_alpha_dummy_1053 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0811 h)

theorem nb078_compact_fv_empty_0812 : (nb078_alpha_dummy_1049) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2678 : (nb078_alpha_dummy_1049) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0812)

theorem nb078_compact_fv_empty_0813 (h : Var) : (nb078_alpha_dummy_1052 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2679 (h : Var) : (nb078_alpha_dummy_1052 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0813 h)

theorem nb078_compact_fv_empty_0814 : (nb078_alpha_dummy_1055) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2680 : (nb078_alpha_dummy_1055) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0814)

theorem nb078_compact_fv_empty_0815 (h : Var) : (nb078_alpha_dummy_1056 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2681 (h : Var) : (nb078_alpha_dummy_1056 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0815 h)

theorem nb078_compact_fv_empty_0816 : (nb078_alpha_dummy_1047) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2682 : (nb078_alpha_dummy_1047) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0816)

theorem nb078_compact_fv_empty_0817 (h : Var) : (nb078_alpha_dummy_1048 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2683 (h : Var) : (nb078_alpha_dummy_1048 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0817 h)

theorem nb078_compact_fv_empty_0818 : (nb078_alpha_dummy_1045) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2684 : (nb078_alpha_dummy_1045) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0818)

theorem nb078_compact_fv_empty_0819 (h : Var) : (nb078_alpha_dummy_1046 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2685 (h : Var) : (nb078_alpha_dummy_1046 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0819 h)

theorem nb078_compact_envfresh_0446 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1073) (nb078_alpha_dummy_1076 h) (nb078_wpp_notmem_2656) (nb078_wpp_notmem_2657 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1072) (nb078_alpha_dummy_1075 h) (nb078_wpp_notmem_2658) (nb078_wpp_notmem_2659 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1071) (nb078_alpha_dummy_1074 h) (nb078_wpp_notmem_2660) (nb078_wpp_notmem_2661 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1069) (nb078_alpha_dummy_1070 h) (nb078_wpp_notmem_2662) (nb078_wpp_notmem_2663 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1065) (nb078_alpha_dummy_1067 h) (nb078_wpp_notmem_2664) (nb078_wpp_notmem_2665 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1066) (nb078_alpha_dummy_1068 h) (nb078_wpp_notmem_2666) (nb078_wpp_notmem_2667 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1058) (nb078_alpha_dummy_1060 h) (nb078_wpp_notmem_2668) (nb078_wpp_notmem_2669 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1057) (nb078_alpha_dummy_1059 h) (nb078_wpp_notmem_2670) (nb078_wpp_notmem_2671 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1063) (nb078_alpha_dummy_1064 h) (nb078_wpp_notmem_2672) (nb078_wpp_notmem_2673 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1061) (nb078_alpha_dummy_1062 h) (nb078_wpp_notmem_2674) (nb078_wpp_notmem_2675 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2676) (nb078_wpp_notmem_2677 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2678) (nb078_wpp_notmem_2679 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2680) (nb078_wpp_notmem_2681 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2682) (nb078_wpp_notmem_2683 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2684) (nb078_wpp_notmem_2685 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb078_wpp_refl_0446 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0446 x y h)

theorem nb078_wpp_notmem_2686 : (nb078_alpha_dummy_1073) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0790)

theorem nb078_wpp_notmem_2687 (h : Var) : (nb078_alpha_dummy_1076 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0791 h)

theorem nb078_wpp_notmem_2688 : (nb078_alpha_dummy_1072) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0792)

theorem nb078_wpp_notmem_2689 (h : Var) : (nb078_alpha_dummy_1075 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0793 h)

theorem nb078_wpp_notmem_2690 : (nb078_alpha_dummy_1071) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0794)

theorem nb078_wpp_notmem_2691 (h : Var) : (nb078_alpha_dummy_1074 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0795 h)

theorem nb078_wpp_notmem_2692 : (nb078_alpha_dummy_1069) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0796)

theorem nb078_wpp_notmem_2693 (h : Var) : (nb078_alpha_dummy_1070 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0797 h)

theorem nb078_wpp_notmem_2694 : (nb078_alpha_dummy_1065) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0798)

theorem nb078_wpp_notmem_2695 (h : Var) : (nb078_alpha_dummy_1067 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0799 h)

theorem nb078_wpp_notmem_2696 : (nb078_alpha_dummy_1066) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0800)

theorem nb078_wpp_notmem_2697 (h : Var) : (nb078_alpha_dummy_1068 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0801 h)

theorem nb078_wpp_notmem_2698 : (nb078_alpha_dummy_1058) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0802)

theorem nb078_wpp_notmem_2699 (h : Var) : (nb078_alpha_dummy_1060 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0803 h)

theorem nb078_wpp_notmem_2700 : (nb078_alpha_dummy_1057) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0804)

theorem nb078_wpp_notmem_2701 (h : Var) : (nb078_alpha_dummy_1059 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0805 h)

theorem nb078_wpp_notmem_2702 : (nb078_alpha_dummy_1063) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0806)

theorem nb078_wpp_notmem_2703 (h : Var) : (nb078_alpha_dummy_1064 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0807 h)

theorem nb078_wpp_notmem_2704 : (nb078_alpha_dummy_1061) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0808)

theorem nb078_wpp_notmem_2705 (h : Var) : (nb078_alpha_dummy_1062 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0809 h)

theorem nb078_wpp_notmem_2706 : (nb078_alpha_dummy_1050) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0810)

theorem nb078_wpp_notmem_2707 (h : Var) : (nb078_alpha_dummy_1053 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0811 h)

theorem nb078_wpp_notmem_2708 : (nb078_alpha_dummy_1049) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0812)

theorem nb078_wpp_notmem_2709 (h : Var) : (nb078_alpha_dummy_1052 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0813 h)

theorem nb078_wpp_notmem_2710 : (nb078_alpha_dummy_1055) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0814)

theorem nb078_wpp_notmem_2711 (h : Var) : (nb078_alpha_dummy_1056 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0815 h)

theorem nb078_wpp_notmem_2712 : (nb078_alpha_dummy_1047) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0816)

theorem nb078_wpp_notmem_2713 (h : Var) : (nb078_alpha_dummy_1048 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0817 h)

theorem nb078_wpp_notmem_2714 : (nb078_alpha_dummy_1045) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0818)

theorem nb078_wpp_notmem_2715 (h : Var) : (nb078_alpha_dummy_1046 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0819 h)

theorem nb078_compact_envfresh_0447 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1073) (nb078_alpha_dummy_1076 h) (nb078_wpp_notmem_2686) (nb078_wpp_notmem_2687 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1072) (nb078_alpha_dummy_1075 h) (nb078_wpp_notmem_2688) (nb078_wpp_notmem_2689 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1071) (nb078_alpha_dummy_1074 h) (nb078_wpp_notmem_2690) (nb078_wpp_notmem_2691 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1069) (nb078_alpha_dummy_1070 h) (nb078_wpp_notmem_2692) (nb078_wpp_notmem_2693 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1065) (nb078_alpha_dummy_1067 h) (nb078_wpp_notmem_2694) (nb078_wpp_notmem_2695 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1066) (nb078_alpha_dummy_1068 h) (nb078_wpp_notmem_2696) (nb078_wpp_notmem_2697 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1058) (nb078_alpha_dummy_1060 h) (nb078_wpp_notmem_2698) (nb078_wpp_notmem_2699 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1057) (nb078_alpha_dummy_1059 h) (nb078_wpp_notmem_2700) (nb078_wpp_notmem_2701 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1063) (nb078_alpha_dummy_1064 h) (nb078_wpp_notmem_2702) (nb078_wpp_notmem_2703 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1061) (nb078_alpha_dummy_1062 h) (nb078_wpp_notmem_2704) (nb078_wpp_notmem_2705 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2706) (nb078_wpp_notmem_2707 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2708) (nb078_wpp_notmem_2709 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2710) (nb078_wpp_notmem_2711 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2712) (nb078_wpp_notmem_2713 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2714) (nb078_wpp_notmem_2715 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb078_wpp_refl_0447 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0447 x y h)

theorem nb078_wpp_notmem_2716 : (nb078_alpha_dummy_1069) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0796)

theorem nb078_wpp_notmem_2717 (h : Var) : (nb078_alpha_dummy_1070 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0797 h)

theorem nb078_wpp_notmem_2718 : (nb078_alpha_dummy_1065) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0798)

theorem nb078_wpp_notmem_2719 (h : Var) : (nb078_alpha_dummy_1067 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0799 h)

theorem nb078_wpp_notmem_2720 : (nb078_alpha_dummy_1066) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0800)

theorem nb078_wpp_notmem_2721 (h : Var) : (nb078_alpha_dummy_1068 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0801 h)

theorem nb078_wpp_notmem_2722 : (nb078_alpha_dummy_1058) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0802)

theorem nb078_wpp_notmem_2723 (h : Var) : (nb078_alpha_dummy_1060 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0803 h)

theorem nb078_wpp_notmem_2724 : (nb078_alpha_dummy_1057) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0804)

theorem nb078_wpp_notmem_2725 (h : Var) : (nb078_alpha_dummy_1059 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0805 h)

theorem nb078_wpp_notmem_2726 : (nb078_alpha_dummy_1063) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0806)

theorem nb078_wpp_notmem_2727 (h : Var) : (nb078_alpha_dummy_1064 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0807 h)

theorem nb078_wpp_notmem_2728 : (nb078_alpha_dummy_1061) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0808)

theorem nb078_wpp_notmem_2729 (h : Var) : (nb078_alpha_dummy_1062 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0809 h)

theorem nb078_wpp_notmem_2730 : (nb078_alpha_dummy_1050) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0810)

theorem nb078_wpp_notmem_2731 (h : Var) : (nb078_alpha_dummy_1053 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0811 h)

theorem nb078_wpp_notmem_2732 : (nb078_alpha_dummy_1049) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0812)

theorem nb078_wpp_notmem_2733 (h : Var) : (nb078_alpha_dummy_1052 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0813 h)

theorem nb078_wpp_notmem_2734 : (nb078_alpha_dummy_1055) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0814)

theorem nb078_wpp_notmem_2735 (h : Var) : (nb078_alpha_dummy_1056 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0815 h)

theorem nb078_wpp_notmem_2736 : (nb078_alpha_dummy_1047) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0816)

theorem nb078_wpp_notmem_2737 (h : Var) : (nb078_alpha_dummy_1048 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0817 h)

theorem nb078_wpp_notmem_2738 : (nb078_alpha_dummy_1045) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0818)

theorem nb078_wpp_notmem_2739 (h : Var) : (nb078_alpha_dummy_1046 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0819 h)

theorem nb078_compact_envfresh_0448 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1069) (nb078_alpha_dummy_1070 h) (nb078_wpp_notmem_2716) (nb078_wpp_notmem_2717 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1065) (nb078_alpha_dummy_1067 h) (nb078_wpp_notmem_2718) (nb078_wpp_notmem_2719 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1066) (nb078_alpha_dummy_1068 h) (nb078_wpp_notmem_2720) (nb078_wpp_notmem_2721 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1058) (nb078_alpha_dummy_1060 h) (nb078_wpp_notmem_2722) (nb078_wpp_notmem_2723 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1057) (nb078_alpha_dummy_1059 h) (nb078_wpp_notmem_2724) (nb078_wpp_notmem_2725 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1063) (nb078_alpha_dummy_1064 h) (nb078_wpp_notmem_2726) (nb078_wpp_notmem_2727 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1061) (nb078_alpha_dummy_1062 h) (nb078_wpp_notmem_2728) (nb078_wpp_notmem_2729 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2730) (nb078_wpp_notmem_2731 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2732) (nb078_wpp_notmem_2733 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2734) (nb078_wpp_notmem_2735 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2736) (nb078_wpp_notmem_2737 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2738) (nb078_wpp_notmem_2739 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0448 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0448 x y h)

noncomputable def nb078_split_alpha_0134 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1063)) (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1063)) (Class.cab (nb078_alpha_dummy_1057) (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1057)) (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1064 h)) (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1064 h)) (Class.cab (nb078_alpha_dummy_1059 h) (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1105 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1101) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1103 h) 0)) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1107 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1106) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1107 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1060 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1110) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1111 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1111 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0446 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1115 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1113 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1119 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1117 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1115 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1113 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1119 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1117 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0447 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1123 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1121 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1123 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1121 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1127 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1125 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1127 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1125 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0448 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0448 x y h)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1105 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1101) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1103 h) 0)) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1053 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1107 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1106) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1107 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1058))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1060 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1110) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1111 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1111 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0446 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1115 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1113 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1119 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1117 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1115 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1113 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1118) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1119 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1117 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0447 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1123 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1121 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1123 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1120) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1121 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1127 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1125 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1127 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1124) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1125 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0448 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1109 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1063), (nb078_alpha_dummy_1064 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0448 x y h))))))))))))))))))))))))))))

theorem nb078_compact_fv_empty_0820 : (nb078_alpha_dummy_1091) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2740 : (nb078_alpha_dummy_1091) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0820)

theorem nb078_compact_fv_empty_0821 (h : Var) : (nb078_alpha_dummy_1092 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2741 (h : Var) : (nb078_alpha_dummy_1092 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0821 h)

theorem nb078_compact_fv_empty_0822 : (nb078_alpha_dummy_1089) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2742 : (nb078_alpha_dummy_1089) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0822)

theorem nb078_compact_fv_empty_0823 (h : Var) : (nb078_alpha_dummy_1090 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2743 (h : Var) : (nb078_alpha_dummy_1090 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0823 h)

theorem nb078_compact_fv_empty_0824 : (nb078_alpha_dummy_1087) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2744 : (nb078_alpha_dummy_1087) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0824)

theorem nb078_compact_fv_empty_0825 (h : Var) : (nb078_alpha_dummy_1088 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2745 (h : Var) : (nb078_alpha_dummy_1088 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0825 h)

theorem nb078_compact_envfresh_0449 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1073), (nb078_alpha_dummy_1076 h)), ((nb078_alpha_dummy_1072), (nb078_alpha_dummy_1075 h)), ((nb078_alpha_dummy_1071), (nb078_alpha_dummy_1074 h)), ((nb078_alpha_dummy_1069), (nb078_alpha_dummy_1070 h)), ((nb078_alpha_dummy_1065), (nb078_alpha_dummy_1067 h)), ((nb078_alpha_dummy_1066), (nb078_alpha_dummy_1068 h)), ((nb078_alpha_dummy_1091), (nb078_alpha_dummy_1092 h)), ((nb078_alpha_dummy_1089), (nb078_alpha_dummy_1090 h)), ((nb078_alpha_dummy_1058), (nb078_alpha_dummy_1060 h)), ((nb078_alpha_dummy_1057), (nb078_alpha_dummy_1059 h)), ((nb078_alpha_dummy_1087), (nb078_alpha_dummy_1088 h)), ((nb078_alpha_dummy_1061), (nb078_alpha_dummy_1062 h)), ((nb078_alpha_dummy_1050), (nb078_alpha_dummy_1053 h)), ((nb078_alpha_dummy_1049), (nb078_alpha_dummy_1052 h)), ((nb078_alpha_dummy_1055), (nb078_alpha_dummy_1056 h)), ((nb078_alpha_dummy_1047), (nb078_alpha_dummy_1048 h)), ((nb078_alpha_dummy_1045), (nb078_alpha_dummy_1046 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1073) (nb078_alpha_dummy_1076 h) (nb078_wpp_notmem_2656) (nb078_wpp_notmem_2657 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1072) (nb078_alpha_dummy_1075 h) (nb078_wpp_notmem_2658) (nb078_wpp_notmem_2659 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1071) (nb078_alpha_dummy_1074 h) (nb078_wpp_notmem_2660) (nb078_wpp_notmem_2661 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1069) (nb078_alpha_dummy_1070 h) (nb078_wpp_notmem_2662) (nb078_wpp_notmem_2663 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1065) (nb078_alpha_dummy_1067 h) (nb078_wpp_notmem_2664) (nb078_wpp_notmem_2665 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1066) (nb078_alpha_dummy_1068 h) (nb078_wpp_notmem_2666) (nb078_wpp_notmem_2667 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1091) (nb078_alpha_dummy_1092 h) (nb078_wpp_notmem_2740) (nb078_wpp_notmem_2741 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1089) (nb078_alpha_dummy_1090 h) (nb078_wpp_notmem_2742) (nb078_wpp_notmem_2743 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1058) (nb078_alpha_dummy_1060 h) (nb078_wpp_notmem_2668) (nb078_wpp_notmem_2669 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1057) (nb078_alpha_dummy_1059 h) (nb078_wpp_notmem_2670) (nb078_wpp_notmem_2671 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1087) (nb078_alpha_dummy_1088 h) (nb078_wpp_notmem_2744) (nb078_wpp_notmem_2745 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1061) (nb078_alpha_dummy_1062 h) (nb078_wpp_notmem_2674) (nb078_wpp_notmem_2675 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1050) (nb078_alpha_dummy_1053 h) (nb078_wpp_notmem_2676) (nb078_wpp_notmem_2677 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1049) (nb078_alpha_dummy_1052 h) (nb078_wpp_notmem_2678) (nb078_wpp_notmem_2679 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1055) (nb078_alpha_dummy_1056 h) (nb078_wpp_notmem_2680) (nb078_wpp_notmem_2681 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1047) (nb078_alpha_dummy_1048 h) (nb078_wpp_notmem_2682) (nb078_wpp_notmem_2683 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1045) (nb078_alpha_dummy_1046 h) (nb078_wpp_notmem_2684) (nb078_wpp_notmem_2685 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
