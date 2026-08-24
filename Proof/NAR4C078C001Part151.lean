import NAR4C078C001Part150

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

theorem nb078_wpp_notmem_2543 (h : Var) : (nb078_alpha_dummy_1028 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0765 h)

theorem nb078_compact_fv_empty_0766 : (nb078_alpha_dummy_1024) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2544 : (nb078_alpha_dummy_1024) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0766)

theorem nb078_compact_fv_empty_0767 (h : Var) : (nb078_alpha_dummy_1027 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2545 (h : Var) : (nb078_alpha_dummy_1027 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0767 h)

theorem nb078_compact_fv_empty_0768 : (nb078_alpha_dummy_1023) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2546 : (nb078_alpha_dummy_1023) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0768)

theorem nb078_compact_fv_empty_0769 (h : Var) : (nb078_alpha_dummy_1026 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2547 (h : Var) : (nb078_alpha_dummy_1026 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0769 h)

theorem nb078_compact_fv_empty_0770 : (nb078_alpha_dummy_1021) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2548 : (nb078_alpha_dummy_1021) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0770)

theorem nb078_compact_fv_empty_0771 (h : Var) : (nb078_alpha_dummy_1022 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2549 (h : Var) : (nb078_alpha_dummy_1022 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0771 h)

theorem nb078_compact_fv_empty_0772 : (nb078_alpha_dummy_1017) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2550 : (nb078_alpha_dummy_1017) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0772)

theorem nb078_compact_fv_empty_0773 (h : Var) : (nb078_alpha_dummy_1019 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2551 (h : Var) : (nb078_alpha_dummy_1019 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0773 h)

theorem nb078_compact_fv_empty_0774 : (nb078_alpha_dummy_1018) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2552 : (nb078_alpha_dummy_1018) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0774)

theorem nb078_compact_fv_empty_0775 (h : Var) : (nb078_alpha_dummy_1020 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2553 (h : Var) : (nb078_alpha_dummy_1020 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0775 h)

theorem nb078_compact_fv_empty_0776 : (nb078_alpha_dummy_1010) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2554 : (nb078_alpha_dummy_1010) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0776)

theorem nb078_compact_fv_empty_0777 (h : Var) : (nb078_alpha_dummy_1012 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2555 (h : Var) : (nb078_alpha_dummy_1012 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0777 h)

theorem nb078_compact_fv_empty_0778 : (nb078_alpha_dummy_1009) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2556 : (nb078_alpha_dummy_1009) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0778)

theorem nb078_compact_fv_empty_0779 (h : Var) : (nb078_alpha_dummy_1011 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2557 (h : Var) : (nb078_alpha_dummy_1011 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0779 h)

theorem nb078_compact_fv_empty_0780 : (nb078_alpha_dummy_1015) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2558 : (nb078_alpha_dummy_1015) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0780)

theorem nb078_compact_fv_empty_0781 (h : Var) : (nb078_alpha_dummy_1016 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2559 (h : Var) : (nb078_alpha_dummy_1016 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0781 h)

theorem nb078_compact_fv_empty_0782 : (nb078_alpha_dummy_1013) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2560 : (nb078_alpha_dummy_1013) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0782)

theorem nb078_compact_fv_empty_0783 (h : Var) : (nb078_alpha_dummy_1014 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2561 (h : Var) : (nb078_alpha_dummy_1014 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0783 h)

theorem nb078_wpp_notmem_2562 : (nb078_alpha_dummy_1006) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0756)

theorem nb078_wpp_notmem_2563 (h : Var) : (nb078_alpha_dummy_1008 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0757 h)

theorem nb078_wpp_notmem_2564 : (nb078_alpha_dummy_1005) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0758)

theorem nb078_wpp_notmem_2565 (h : Var) : (nb078_alpha_dummy_1007 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0759 h)

theorem nb078_wpp_notmem_2566 : (nb078_alpha_dummy_1003) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0760)

theorem nb078_wpp_notmem_2567 (y : Var) (h : Var) : (nb078_alpha_dummy_1004 y h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0761 y h)

theorem nb078_wpp_notmem_2568 : (nb078_alpha_dummy_1001) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0762)

theorem nb078_wpp_notmem_2569 (y : Var) (h : Var) : (nb078_alpha_dummy_1002 y h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0763 y h)

theorem nb078_compact_envfresh_0431 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1025) (nb078_alpha_dummy_1028 h) (nb078_wpp_notmem_2542) (nb078_wpp_notmem_2543 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1024) (nb078_alpha_dummy_1027 h) (nb078_wpp_notmem_2544) (nb078_wpp_notmem_2545 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1023) (nb078_alpha_dummy_1026 h) (nb078_wpp_notmem_2546) (nb078_wpp_notmem_2547 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1021) (nb078_alpha_dummy_1022 h) (nb078_wpp_notmem_2548) (nb078_wpp_notmem_2549 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1017) (nb078_alpha_dummy_1019 h) (nb078_wpp_notmem_2550) (nb078_wpp_notmem_2551 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1018) (nb078_alpha_dummy_1020 h) (nb078_wpp_notmem_2552) (nb078_wpp_notmem_2553 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1010) (nb078_alpha_dummy_1012 h) (nb078_wpp_notmem_2554) (nb078_wpp_notmem_2555 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1009) (nb078_alpha_dummy_1011 h) (nb078_wpp_notmem_2556) (nb078_wpp_notmem_2557 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1015) (nb078_alpha_dummy_1016 h) (nb078_wpp_notmem_2558) (nb078_wpp_notmem_2559 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1013) (nb078_alpha_dummy_1014 h) (nb078_wpp_notmem_2560) (nb078_wpp_notmem_2561 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1006) (nb078_alpha_dummy_1008 h) (nb078_wpp_notmem_2562) (nb078_wpp_notmem_2563 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1005) (nb078_alpha_dummy_1007 h) (nb078_wpp_notmem_2564) (nb078_wpp_notmem_2565 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1003) (nb078_alpha_dummy_1004 y h) (nb078_wpp_notmem_2566) (nb078_wpp_notmem_2567 y h) (TEnvFresh.consFresh (nb078_alpha_dummy_1001) (nb078_alpha_dummy_1002 y h) (nb078_wpp_notmem_2568) (nb078_wpp_notmem_2569 y h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0431 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0431 x y h)

theorem nb078_wpp_notmem_2570 : (nb078_alpha_dummy_1025) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0764)

theorem nb078_wpp_notmem_2571 (h : Var) : (nb078_alpha_dummy_1028 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0765 h)

theorem nb078_wpp_notmem_2572 : (nb078_alpha_dummy_1024) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0766)

theorem nb078_wpp_notmem_2573 (h : Var) : (nb078_alpha_dummy_1027 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0767 h)

theorem nb078_wpp_notmem_2574 : (nb078_alpha_dummy_1023) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0768)

theorem nb078_wpp_notmem_2575 (h : Var) : (nb078_alpha_dummy_1026 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0769 h)

theorem nb078_wpp_notmem_2576 : (nb078_alpha_dummy_1021) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0770)

theorem nb078_wpp_notmem_2577 (h : Var) : (nb078_alpha_dummy_1022 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0771 h)

theorem nb078_wpp_notmem_2578 : (nb078_alpha_dummy_1017) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0772)

theorem nb078_wpp_notmem_2579 (h : Var) : (nb078_alpha_dummy_1019 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0773 h)

theorem nb078_wpp_notmem_2580 : (nb078_alpha_dummy_1018) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0774)

theorem nb078_wpp_notmem_2581 (h : Var) : (nb078_alpha_dummy_1020 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0775 h)

theorem nb078_wpp_notmem_2582 : (nb078_alpha_dummy_1010) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0776)

theorem nb078_wpp_notmem_2583 (h : Var) : (nb078_alpha_dummy_1012 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0777 h)

theorem nb078_wpp_notmem_2584 : (nb078_alpha_dummy_1009) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0778)

theorem nb078_wpp_notmem_2585 (h : Var) : (nb078_alpha_dummy_1011 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0779 h)

theorem nb078_wpp_notmem_2586 : (nb078_alpha_dummy_1015) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0780)

theorem nb078_wpp_notmem_2587 (h : Var) : (nb078_alpha_dummy_1016 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0781 h)

theorem nb078_wpp_notmem_2588 : (nb078_alpha_dummy_1013) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0782)

theorem nb078_wpp_notmem_2589 (h : Var) : (nb078_alpha_dummy_1014 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0783 h)

theorem nb078_wpp_notmem_2590 : (nb078_alpha_dummy_1006) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0756)

theorem nb078_wpp_notmem_2591 (h : Var) : (nb078_alpha_dummy_1008 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0757 h)

theorem nb078_wpp_notmem_2592 : (nb078_alpha_dummy_1005) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0758)

theorem nb078_wpp_notmem_2593 (h : Var) : (nb078_alpha_dummy_1007 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0759 h)

theorem nb078_wpp_notmem_2594 : (nb078_alpha_dummy_1003) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0760)

theorem nb078_wpp_notmem_2595 (y : Var) (h : Var) : (nb078_alpha_dummy_1004 y h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0761 y h)

theorem nb078_wpp_notmem_2596 : (nb078_alpha_dummy_1001) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0762)

theorem nb078_wpp_notmem_2597 (y : Var) (h : Var) : (nb078_alpha_dummy_1002 y h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0763 y h)

theorem nb078_compact_envfresh_0432 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1025) (nb078_alpha_dummy_1028 h) (nb078_wpp_notmem_2570) (nb078_wpp_notmem_2571 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1024) (nb078_alpha_dummy_1027 h) (nb078_wpp_notmem_2572) (nb078_wpp_notmem_2573 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1023) (nb078_alpha_dummy_1026 h) (nb078_wpp_notmem_2574) (nb078_wpp_notmem_2575 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1021) (nb078_alpha_dummy_1022 h) (nb078_wpp_notmem_2576) (nb078_wpp_notmem_2577 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1017) (nb078_alpha_dummy_1019 h) (nb078_wpp_notmem_2578) (nb078_wpp_notmem_2579 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1018) (nb078_alpha_dummy_1020 h) (nb078_wpp_notmem_2580) (nb078_wpp_notmem_2581 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1010) (nb078_alpha_dummy_1012 h) (nb078_wpp_notmem_2582) (nb078_wpp_notmem_2583 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1009) (nb078_alpha_dummy_1011 h) (nb078_wpp_notmem_2584) (nb078_wpp_notmem_2585 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1015) (nb078_alpha_dummy_1016 h) (nb078_wpp_notmem_2586) (nb078_wpp_notmem_2587 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1013) (nb078_alpha_dummy_1014 h) (nb078_wpp_notmem_2588) (nb078_wpp_notmem_2589 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1006) (nb078_alpha_dummy_1008 h) (nb078_wpp_notmem_2590) (nb078_wpp_notmem_2591 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1005) (nb078_alpha_dummy_1007 h) (nb078_wpp_notmem_2592) (nb078_wpp_notmem_2593 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1003) (nb078_alpha_dummy_1004 y h) (nb078_wpp_notmem_2594) (nb078_wpp_notmem_2595 y h) (TEnvFresh.consFresh (nb078_alpha_dummy_1001) (nb078_alpha_dummy_1002 y h) (nb078_wpp_notmem_2596) (nb078_wpp_notmem_2597 y h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0432 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0432 x y h)

theorem nb078_wpp_notmem_2598 : (nb078_alpha_dummy_1021) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0770)

theorem nb078_wpp_notmem_2599 (h : Var) : (nb078_alpha_dummy_1022 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0771 h)

theorem nb078_wpp_notmem_2600 : (nb078_alpha_dummy_1017) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0772)

theorem nb078_wpp_notmem_2601 (h : Var) : (nb078_alpha_dummy_1019 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0773 h)

theorem nb078_wpp_notmem_2602 : (nb078_alpha_dummy_1018) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0774)

theorem nb078_wpp_notmem_2603 (h : Var) : (nb078_alpha_dummy_1020 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0775 h)

theorem nb078_wpp_notmem_2604 : (nb078_alpha_dummy_1010) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0776)

theorem nb078_wpp_notmem_2605 (h : Var) : (nb078_alpha_dummy_1012 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0777 h)

theorem nb078_wpp_notmem_2606 : (nb078_alpha_dummy_1009) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0778)

theorem nb078_wpp_notmem_2607 (h : Var) : (nb078_alpha_dummy_1011 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0779 h)

theorem nb078_wpp_notmem_2608 : (nb078_alpha_dummy_1015) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0780)

theorem nb078_wpp_notmem_2609 (h : Var) : (nb078_alpha_dummy_1016 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0781 h)

theorem nb078_wpp_notmem_2610 : (nb078_alpha_dummy_1013) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0782)

theorem nb078_wpp_notmem_2611 (h : Var) : (nb078_alpha_dummy_1014 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0783 h)

theorem nb078_wpp_notmem_2612 : (nb078_alpha_dummy_1006) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0756)

theorem nb078_wpp_notmem_2613 (h : Var) : (nb078_alpha_dummy_1008 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0757 h)

theorem nb078_wpp_notmem_2614 : (nb078_alpha_dummy_1005) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0758)

theorem nb078_wpp_notmem_2615 (h : Var) : (nb078_alpha_dummy_1007 h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0759 h)

theorem nb078_wpp_notmem_2616 : (nb078_alpha_dummy_1003) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0760)

theorem nb078_wpp_notmem_2617 (y : Var) (h : Var) : (nb078_alpha_dummy_1004 y h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0761 y h)

theorem nb078_wpp_notmem_2618 : (nb078_alpha_dummy_1001) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0762)

theorem nb078_wpp_notmem_2619 (y : Var) (h : Var) : (nb078_alpha_dummy_1002 y h) ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0763 y h)

theorem nb078_compact_envfresh_0433 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1021) (nb078_alpha_dummy_1022 h) (nb078_wpp_notmem_2598) (nb078_wpp_notmem_2599 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1017) (nb078_alpha_dummy_1019 h) (nb078_wpp_notmem_2600) (nb078_wpp_notmem_2601 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1018) (nb078_alpha_dummy_1020 h) (nb078_wpp_notmem_2602) (nb078_wpp_notmem_2603 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1010) (nb078_alpha_dummy_1012 h) (nb078_wpp_notmem_2604) (nb078_wpp_notmem_2605 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1009) (nb078_alpha_dummy_1011 h) (nb078_wpp_notmem_2606) (nb078_wpp_notmem_2607 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1015) (nb078_alpha_dummy_1016 h) (nb078_wpp_notmem_2608) (nb078_wpp_notmem_2609 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1013) (nb078_alpha_dummy_1014 h) (nb078_wpp_notmem_2610) (nb078_wpp_notmem_2611 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1006) (nb078_alpha_dummy_1008 h) (nb078_wpp_notmem_2612) (nb078_wpp_notmem_2613 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1005) (nb078_alpha_dummy_1007 h) (nb078_wpp_notmem_2614) (nb078_wpp_notmem_2615 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1003) (nb078_alpha_dummy_1004 y h) (nb078_wpp_notmem_2616) (nb078_wpp_notmem_2617 y h) (TEnvFresh.consFresh (nb078_alpha_dummy_1001) (nb078_alpha_dummy_1002 y h) (nb078_wpp_notmem_2618) (nb078_wpp_notmem_2619 y h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb078_wpp_refl_0433 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0433 x y h)

noncomputable def nb078_split_alpha_0130 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1015)) (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1015)) (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_1016 h)) (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_1016 h)) (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1053 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1049) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1051 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1055 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1054) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1055 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1012 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1058) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1059 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1059 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1057 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0431 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1063 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1061 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1067 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1065 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1063 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1061 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1067 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1065 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0432 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1071 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1069 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1071 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1069 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1075 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1073 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1075 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1073 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1057 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0433 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1057 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1057 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0433 x y h)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1053 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1049) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1051 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1055 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1054) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1055 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1012 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1058) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1059 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1059 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1057 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0431 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1063 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1061 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1067 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1065 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1063 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1061 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1067 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1065 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0432 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1071 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1069 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1071 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1069 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1075 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1073 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1075 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1073 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1057 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0433 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1057 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1057 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1015), (nb078_alpha_dummy_1016 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0433 x y h))))))))))))))))))))))))))))

theorem nb078_compact_fv_empty_0784 : (nb078_alpha_dummy_1043) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2620 : (nb078_alpha_dummy_1043) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0784)

theorem nb078_compact_fv_empty_0785 (h : Var) : (nb078_alpha_dummy_1044 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2621 (h : Var) : (nb078_alpha_dummy_1044 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0785 h)

theorem nb078_compact_fv_empty_0786 : (nb078_alpha_dummy_1041) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2622 : (nb078_alpha_dummy_1041) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0786)

theorem nb078_compact_fv_empty_0787 (h : Var) : (nb078_alpha_dummy_1042 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2623 (h : Var) : (nb078_alpha_dummy_1042 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0787 h)

theorem nb078_compact_fv_empty_0788 : (nb078_alpha_dummy_1039) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2624 : (nb078_alpha_dummy_1039) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0788)

theorem nb078_compact_fv_empty_0789 (h : Var) : (nb078_alpha_dummy_1040 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2625 (h : Var) : (nb078_alpha_dummy_1040 h) ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0789 h)

theorem nb078_compact_envfresh_0434 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_1025) (nb078_alpha_dummy_1028 h) (nb078_wpp_notmem_2542) (nb078_wpp_notmem_2543 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1024) (nb078_alpha_dummy_1027 h) (nb078_wpp_notmem_2544) (nb078_wpp_notmem_2545 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1023) (nb078_alpha_dummy_1026 h) (nb078_wpp_notmem_2546) (nb078_wpp_notmem_2547 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1021) (nb078_alpha_dummy_1022 h) (nb078_wpp_notmem_2548) (nb078_wpp_notmem_2549 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1017) (nb078_alpha_dummy_1019 h) (nb078_wpp_notmem_2550) (nb078_wpp_notmem_2551 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1018) (nb078_alpha_dummy_1020 h) (nb078_wpp_notmem_2552) (nb078_wpp_notmem_2553 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1043) (nb078_alpha_dummy_1044 h) (nb078_wpp_notmem_2620) (nb078_wpp_notmem_2621 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1041) (nb078_alpha_dummy_1042 h) (nb078_wpp_notmem_2622) (nb078_wpp_notmem_2623 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1010) (nb078_alpha_dummy_1012 h) (nb078_wpp_notmem_2554) (nb078_wpp_notmem_2555 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1009) (nb078_alpha_dummy_1011 h) (nb078_wpp_notmem_2556) (nb078_wpp_notmem_2557 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1039) (nb078_alpha_dummy_1040 h) (nb078_wpp_notmem_2624) (nb078_wpp_notmem_2625 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1013) (nb078_alpha_dummy_1014 h) (nb078_wpp_notmem_2560) (nb078_wpp_notmem_2561 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1006) (nb078_alpha_dummy_1008 h) (nb078_wpp_notmem_2562) (nb078_wpp_notmem_2563 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1005) (nb078_alpha_dummy_1007 h) (nb078_wpp_notmem_2564) (nb078_wpp_notmem_2565 h) (TEnvFresh.consFresh (nb078_alpha_dummy_1003) (nb078_alpha_dummy_1004 y h) (nb078_wpp_notmem_2566) (nb078_wpp_notmem_2567 y h) (TEnvFresh.consFresh (nb078_alpha_dummy_1001) (nb078_alpha_dummy_1002 y h) (nb078_wpp_notmem_2568) (nb078_wpp_notmem_2569 y h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0434 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_1025), (nb078_alpha_dummy_1028 h)), ((nb078_alpha_dummy_1024), (nb078_alpha_dummy_1027 h)), ((nb078_alpha_dummy_1023), (nb078_alpha_dummy_1026 h)), ((nb078_alpha_dummy_1021), (nb078_alpha_dummy_1022 h)), ((nb078_alpha_dummy_1017), (nb078_alpha_dummy_1019 h)), ((nb078_alpha_dummy_1018), (nb078_alpha_dummy_1020 h)), ((nb078_alpha_dummy_1043), (nb078_alpha_dummy_1044 h)), ((nb078_alpha_dummy_1041), (nb078_alpha_dummy_1042 h)), ((nb078_alpha_dummy_1010), (nb078_alpha_dummy_1012 h)), ((nb078_alpha_dummy_1009), (nb078_alpha_dummy_1011 h)), ((nb078_alpha_dummy_1039), (nb078_alpha_dummy_1040 h)), ((nb078_alpha_dummy_1013), (nb078_alpha_dummy_1014 h)), ((nb078_alpha_dummy_1006), (nb078_alpha_dummy_1008 h)), ((nb078_alpha_dummy_1005), (nb078_alpha_dummy_1007 h)), ((nb078_alpha_dummy_1003), (nb078_alpha_dummy_1004 y h)), ((nb078_alpha_dummy_1001), (nb078_alpha_dummy_1002 y h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0434 x y h)

theorem nb078_wpp_notmem_2626 : (nb078_alpha_dummy_1043) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0784)

theorem nb078_wpp_notmem_2627 (h : Var) : (nb078_alpha_dummy_1044 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0785 h)

theorem nb078_wpp_notmem_2628 : (nb078_alpha_dummy_1041) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0786)

theorem nb078_wpp_notmem_2629 (h : Var) : (nb078_alpha_dummy_1042 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0787 h)

theorem nb078_wpp_notmem_2630 : (nb078_alpha_dummy_1039) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0788)

theorem nb078_wpp_notmem_2631 (h : Var) : (nb078_alpha_dummy_1040 h) ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0789 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
