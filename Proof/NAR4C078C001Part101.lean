import NAR4C078C001Part100

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

theorem nb078_compact_fv_empty_0554 : (nb078_alpha_dummy_741) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1852 : (nb078_alpha_dummy_741) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_741, fv_syn_c1c] using (nb078_compact_fv_empty_0554)

theorem nb078_compact_fv_empty_0555 (g : Var) : (nb078_alpha_dummy_744 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1853 (g : Var) : (nb078_alpha_dummy_744 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_744, fv_syn_c1c] using (nb078_compact_fv_empty_0555 g)

theorem nb078_compact_fv_empty_0556 : (nb078_alpha_dummy_739) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1854 : (nb078_alpha_dummy_739) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_739, fv_syn_c1c] using (nb078_compact_fv_empty_0556)

theorem nb078_compact_fv_empty_0557 (g : Var) : (nb078_alpha_dummy_740 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1855 (g : Var) : (nb078_alpha_dummy_740 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_740, fv_syn_c1c] using (nb078_compact_fv_empty_0557 g)

theorem nb078_compact_fv_empty_0558 : (nb078_alpha_dummy_735) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1856 : (nb078_alpha_dummy_735) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_735, fv_syn_c1c] using (nb078_compact_fv_empty_0558)

theorem nb078_compact_fv_empty_0559 (g : Var) : (nb078_alpha_dummy_737 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1857 (g : Var) : (nb078_alpha_dummy_737 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_737, fv_syn_c1c] using (nb078_compact_fv_empty_0559 g)

theorem nb078_compact_fv_empty_0560 : (nb078_alpha_dummy_736) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1858 : (nb078_alpha_dummy_736) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_736, fv_syn_c1c] using (nb078_compact_fv_empty_0560)

theorem nb078_compact_fv_empty_0561 (g : Var) : (nb078_alpha_dummy_738 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1859 (g : Var) : (nb078_alpha_dummy_738 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_738, fv_syn_c1c] using (nb078_compact_fv_empty_0561 g)

theorem nb078_compact_fv_empty_0562 : (nb078_alpha_dummy_728) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1860 : (nb078_alpha_dummy_728) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_728, fv_syn_c1c] using (nb078_compact_fv_empty_0562)

theorem nb078_compact_fv_empty_0563 (g : Var) : (nb078_alpha_dummy_730 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1861 (g : Var) : (nb078_alpha_dummy_730 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_730, fv_syn_c1c] using (nb078_compact_fv_empty_0563 g)

theorem nb078_compact_fv_empty_0564 : (nb078_alpha_dummy_727) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1862 : (nb078_alpha_dummy_727) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_727, fv_syn_c1c] using (nb078_compact_fv_empty_0564)

theorem nb078_compact_fv_empty_0565 (g : Var) : (nb078_alpha_dummy_729 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1863 (g : Var) : (nb078_alpha_dummy_729 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_729, fv_syn_c1c] using (nb078_compact_fv_empty_0565 g)

theorem nb078_compact_fv_empty_0566 : (nb078_alpha_dummy_733) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1864 : (nb078_alpha_dummy_733) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_733, fv_syn_c1c] using (nb078_compact_fv_empty_0566)

theorem nb078_compact_fv_empty_0567 (g : Var) : (nb078_alpha_dummy_734 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1865 (g : Var) : (nb078_alpha_dummy_734 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_734, fv_syn_c1c] using (nb078_compact_fv_empty_0567 g)

theorem nb078_compact_fv_empty_0568 : (nb078_alpha_dummy_731) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1866 : (nb078_alpha_dummy_731) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_731, fv_syn_c1c] using (nb078_compact_fv_empty_0568)

theorem nb078_compact_fv_empty_0569 (g : Var) : (nb078_alpha_dummy_732 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1867 (g : Var) : (nb078_alpha_dummy_732 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_732, fv_syn_c1c] using (nb078_compact_fv_empty_0569 g)

theorem nb078_compact_envfresh_0252 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_743) (nb078_alpha_dummy_746 g) (nb078_wpp_notmem_1848) (nb078_wpp_notmem_1849 g) (TEnvFresh.consFresh (nb078_alpha_dummy_742) (nb078_alpha_dummy_745 g) (nb078_wpp_notmem_1850) (nb078_wpp_notmem_1851 g) (TEnvFresh.consFresh (nb078_alpha_dummy_741) (nb078_alpha_dummy_744 g) (nb078_wpp_notmem_1852) (nb078_wpp_notmem_1853 g) (TEnvFresh.consFresh (nb078_alpha_dummy_739) (nb078_alpha_dummy_740 g) (nb078_wpp_notmem_1854) (nb078_wpp_notmem_1855 g) (TEnvFresh.consFresh (nb078_alpha_dummy_735) (nb078_alpha_dummy_737 g) (nb078_wpp_notmem_1856) (nb078_wpp_notmem_1857 g) (TEnvFresh.consFresh (nb078_alpha_dummy_736) (nb078_alpha_dummy_738 g) (nb078_wpp_notmem_1858) (nb078_wpp_notmem_1859 g) (TEnvFresh.consFresh (nb078_alpha_dummy_728) (nb078_alpha_dummy_730 g) (nb078_wpp_notmem_1860) (nb078_wpp_notmem_1861 g) (TEnvFresh.consFresh (nb078_alpha_dummy_727) (nb078_alpha_dummy_729 g) (nb078_wpp_notmem_1862) (nb078_wpp_notmem_1863 g) (TEnvFresh.consFresh (nb078_alpha_dummy_733) (nb078_alpha_dummy_734 g) (nb078_wpp_notmem_1864) (nb078_wpp_notmem_1865 g) (TEnvFresh.consFresh (nb078_alpha_dummy_731) (nb078_alpha_dummy_732 g) (nb078_wpp_notmem_1866) (nb078_wpp_notmem_1867 g) (TEnvFresh.consFresh (nb078_alpha_dummy_571) (nb078_alpha_dummy_574 g) (nb078_wpp_notmem_1590) (nb078_wpp_notmem_1591 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1468) (nb078_wpp_notmem_1469 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1470) (nb078_wpp_notmem_1471 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1472) (nb078_wpp_notmem_1473 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1474) (nb078_wpp_notmem_1475 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1476) (nb078_wpp_notmem_1477 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0252 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0252 x y g)

theorem nb078_wpp_notmem_1868 : (nb078_alpha_dummy_743) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_743, fv_syn_c0] using (nb078_compact_fv_empty_0550)

theorem nb078_wpp_notmem_1869 (g : Var) : (nb078_alpha_dummy_746 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_746, fv_syn_c0] using (nb078_compact_fv_empty_0551 g)

theorem nb078_wpp_notmem_1870 : (nb078_alpha_dummy_742) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_742, fv_syn_c0] using (nb078_compact_fv_empty_0552)

theorem nb078_wpp_notmem_1871 (g : Var) : (nb078_alpha_dummy_745 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_745, fv_syn_c0] using (nb078_compact_fv_empty_0553 g)

theorem nb078_wpp_notmem_1872 : (nb078_alpha_dummy_741) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_741, fv_syn_c0] using (nb078_compact_fv_empty_0554)

theorem nb078_wpp_notmem_1873 (g : Var) : (nb078_alpha_dummy_744 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_744, fv_syn_c0] using (nb078_compact_fv_empty_0555 g)

theorem nb078_wpp_notmem_1874 : (nb078_alpha_dummy_739) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_739, fv_syn_c0] using (nb078_compact_fv_empty_0556)

theorem nb078_wpp_notmem_1875 (g : Var) : (nb078_alpha_dummy_740 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_740, fv_syn_c0] using (nb078_compact_fv_empty_0557 g)

theorem nb078_wpp_notmem_1876 : (nb078_alpha_dummy_735) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_735, fv_syn_c0] using (nb078_compact_fv_empty_0558)

theorem nb078_wpp_notmem_1877 (g : Var) : (nb078_alpha_dummy_737 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_737, fv_syn_c0] using (nb078_compact_fv_empty_0559 g)

theorem nb078_wpp_notmem_1878 : (nb078_alpha_dummy_736) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_736, fv_syn_c0] using (nb078_compact_fv_empty_0560)

theorem nb078_wpp_notmem_1879 (g : Var) : (nb078_alpha_dummy_738 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_738, fv_syn_c0] using (nb078_compact_fv_empty_0561 g)

theorem nb078_wpp_notmem_1880 : (nb078_alpha_dummy_728) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_728, fv_syn_c0] using (nb078_compact_fv_empty_0562)

theorem nb078_wpp_notmem_1881 (g : Var) : (nb078_alpha_dummy_730 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_730, fv_syn_c0] using (nb078_compact_fv_empty_0563 g)

theorem nb078_wpp_notmem_1882 : (nb078_alpha_dummy_727) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_727, fv_syn_c0] using (nb078_compact_fv_empty_0564)

theorem nb078_wpp_notmem_1883 (g : Var) : (nb078_alpha_dummy_729 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_729, fv_syn_c0] using (nb078_compact_fv_empty_0565 g)

theorem nb078_wpp_notmem_1884 : (nb078_alpha_dummy_733) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_733, fv_syn_c0] using (nb078_compact_fv_empty_0566)

theorem nb078_wpp_notmem_1885 (g : Var) : (nb078_alpha_dummy_734 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_734, fv_syn_c0] using (nb078_compact_fv_empty_0567 g)

theorem nb078_wpp_notmem_1886 : (nb078_alpha_dummy_731) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_731, fv_syn_c0] using (nb078_compact_fv_empty_0568)

theorem nb078_wpp_notmem_1887 (g : Var) : (nb078_alpha_dummy_732 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_732, fv_syn_c0] using (nb078_compact_fv_empty_0569 g)

theorem nb078_compact_envfresh_0253 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_743) (nb078_alpha_dummy_746 g) (nb078_wpp_notmem_1868) (nb078_wpp_notmem_1869 g) (TEnvFresh.consFresh (nb078_alpha_dummy_742) (nb078_alpha_dummy_745 g) (nb078_wpp_notmem_1870) (nb078_wpp_notmem_1871 g) (TEnvFresh.consFresh (nb078_alpha_dummy_741) (nb078_alpha_dummy_744 g) (nb078_wpp_notmem_1872) (nb078_wpp_notmem_1873 g) (TEnvFresh.consFresh (nb078_alpha_dummy_739) (nb078_alpha_dummy_740 g) (nb078_wpp_notmem_1874) (nb078_wpp_notmem_1875 g) (TEnvFresh.consFresh (nb078_alpha_dummy_735) (nb078_alpha_dummy_737 g) (nb078_wpp_notmem_1876) (nb078_wpp_notmem_1877 g) (TEnvFresh.consFresh (nb078_alpha_dummy_736) (nb078_alpha_dummy_738 g) (nb078_wpp_notmem_1878) (nb078_wpp_notmem_1879 g) (TEnvFresh.consFresh (nb078_alpha_dummy_728) (nb078_alpha_dummy_730 g) (nb078_wpp_notmem_1880) (nb078_wpp_notmem_1881 g) (TEnvFresh.consFresh (nb078_alpha_dummy_727) (nb078_alpha_dummy_729 g) (nb078_wpp_notmem_1882) (nb078_wpp_notmem_1883 g) (TEnvFresh.consFresh (nb078_alpha_dummy_733) (nb078_alpha_dummy_734 g) (nb078_wpp_notmem_1884) (nb078_wpp_notmem_1885 g) (TEnvFresh.consFresh (nb078_alpha_dummy_731) (nb078_alpha_dummy_732 g) (nb078_wpp_notmem_1886) (nb078_wpp_notmem_1887 g) (TEnvFresh.consFresh (nb078_alpha_dummy_571) (nb078_alpha_dummy_574 g) (nb078_wpp_notmem_1612) (nb078_wpp_notmem_1613 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1498) (nb078_wpp_notmem_1499 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1500) (nb078_wpp_notmem_1501 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1502) (nb078_wpp_notmem_1503 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1504) (nb078_wpp_notmem_1505 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1506) (nb078_wpp_notmem_1507 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0788) (nb078_wpp_notmem_0789 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0253 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0253 x y g)

theorem nb078_wpp_notmem_1888 : (nb078_alpha_dummy_739) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_739, fv_syn_cnnc] using (nb078_compact_fv_empty_0556)

theorem nb078_wpp_notmem_1889 (g : Var) : (nb078_alpha_dummy_740 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_740, fv_syn_cnnc] using (nb078_compact_fv_empty_0557 g)

theorem nb078_wpp_notmem_1890 : (nb078_alpha_dummy_735) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_735, fv_syn_cnnc] using (nb078_compact_fv_empty_0558)

theorem nb078_wpp_notmem_1891 (g : Var) : (nb078_alpha_dummy_737 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_737, fv_syn_cnnc] using (nb078_compact_fv_empty_0559 g)

theorem nb078_wpp_notmem_1892 : (nb078_alpha_dummy_736) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_736, fv_syn_cnnc] using (nb078_compact_fv_empty_0560)

theorem nb078_wpp_notmem_1893 (g : Var) : (nb078_alpha_dummy_738 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_738, fv_syn_cnnc] using (nb078_compact_fv_empty_0561 g)

theorem nb078_wpp_notmem_1894 : (nb078_alpha_dummy_728) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_728, fv_syn_cnnc] using (nb078_compact_fv_empty_0562)

theorem nb078_wpp_notmem_1895 (g : Var) : (nb078_alpha_dummy_730 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_730, fv_syn_cnnc] using (nb078_compact_fv_empty_0563 g)

theorem nb078_wpp_notmem_1896 : (nb078_alpha_dummy_727) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_727, fv_syn_cnnc] using (nb078_compact_fv_empty_0564)

theorem nb078_wpp_notmem_1897 (g : Var) : (nb078_alpha_dummy_729 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_729, fv_syn_cnnc] using (nb078_compact_fv_empty_0565 g)

theorem nb078_wpp_notmem_1898 : (nb078_alpha_dummy_733) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_733, fv_syn_cnnc] using (nb078_compact_fv_empty_0566)

theorem nb078_wpp_notmem_1899 (g : Var) : (nb078_alpha_dummy_734 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_734, fv_syn_cnnc] using (nb078_compact_fv_empty_0567 g)

theorem nb078_wpp_notmem_1900 : (nb078_alpha_dummy_731) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_731, fv_syn_cnnc] using (nb078_compact_fv_empty_0568)

theorem nb078_wpp_notmem_1901 (g : Var) : (nb078_alpha_dummy_732 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_732, fv_syn_cnnc] using (nb078_compact_fv_empty_0569 g)

theorem nb078_compact_envfresh_0254 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_739) (nb078_alpha_dummy_740 g) (nb078_wpp_notmem_1888) (nb078_wpp_notmem_1889 g) (TEnvFresh.consFresh (nb078_alpha_dummy_735) (nb078_alpha_dummy_737 g) (nb078_wpp_notmem_1890) (nb078_wpp_notmem_1891 g) (TEnvFresh.consFresh (nb078_alpha_dummy_736) (nb078_alpha_dummy_738 g) (nb078_wpp_notmem_1892) (nb078_wpp_notmem_1893 g) (TEnvFresh.consFresh (nb078_alpha_dummy_728) (nb078_alpha_dummy_730 g) (nb078_wpp_notmem_1894) (nb078_wpp_notmem_1895 g) (TEnvFresh.consFresh (nb078_alpha_dummy_727) (nb078_alpha_dummy_729 g) (nb078_wpp_notmem_1896) (nb078_wpp_notmem_1897 g) (TEnvFresh.consFresh (nb078_alpha_dummy_733) (nb078_alpha_dummy_734 g) (nb078_wpp_notmem_1898) (nb078_wpp_notmem_1899 g) (TEnvFresh.consFresh (nb078_alpha_dummy_731) (nb078_alpha_dummy_732 g) (nb078_wpp_notmem_1900) (nb078_wpp_notmem_1901 g) (TEnvFresh.consFresh (nb078_alpha_dummy_571) (nb078_alpha_dummy_574 g) (nb078_wpp_notmem_1628) (nb078_wpp_notmem_1629 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1522) (nb078_wpp_notmem_1523 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1524) (nb078_wpp_notmem_1525 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1526) (nb078_wpp_notmem_1527 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1528) (nb078_wpp_notmem_1529 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1530) (nb078_wpp_notmem_1531 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0814) (nb078_wpp_notmem_0815 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb078_wpp_refl_0254 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0254 x y g)

noncomputable def nb078_split_alpha_0075 (x : Var) (y : Var) (g : Var) : TAlphaWff [((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_733)) (Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_733)) (Class.cab (nb078_alpha_dummy_727) (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571)) (Wff.classEq (Class.cv (nb078_alpha_dummy_727)) (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_734 g)) (Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_734 g)) (Class.cab (nb078_alpha_dummy_729 g) (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0764) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0765 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0761) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0763 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0766) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0767 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0766) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0767 g) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_728))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_730 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0770) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0771 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0770) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0771 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0768) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0769 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0252 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0774) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0775 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0772) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0773 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0778) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0779 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0776) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0777 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0774) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0775 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0772) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0773 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0778) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0779 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0776) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0777 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0253 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0782) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0783 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0780) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0781 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0782) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0783 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0780) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0781 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0786) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0787 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0784) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0785 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0786) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0787 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0784) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0785 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0768) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0769 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0254 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0768) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0769 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0768) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0769 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0254 x y g)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0764) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0765 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0761) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0763 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0766) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0767 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0766) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0767 g) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_728))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_730 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0770) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0771 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0770) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0771 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0768) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0769 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0252 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0774) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0775 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0772) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0773 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0778) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0779 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0776) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0777 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0774) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0775 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0772) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0773 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0778) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0779 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0776) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0777 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0253 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0782) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0783 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0780) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0781 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0782) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0783 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0780) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0781 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0786) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0787 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0784) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0785 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0786) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0787 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0784) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0785 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0768) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0769 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0254 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0768) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0769 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0768) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0769 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0254 x y g))))))))))))))))))))))))))))

theorem nb078_compact_fv_empty_0570 : (nb078_alpha_dummy_761) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1902 : (nb078_alpha_dummy_761) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_761, fv_syn_c1c] using (nb078_compact_fv_empty_0570)

theorem nb078_compact_fv_empty_0571 (g : Var) : (nb078_alpha_dummy_762 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1903 (g : Var) : (nb078_alpha_dummy_762 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_762, fv_syn_c1c] using (nb078_compact_fv_empty_0571 g)

theorem nb078_compact_fv_empty_0572 : (nb078_alpha_dummy_759) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1904 : (nb078_alpha_dummy_759) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_759, fv_syn_c1c] using (nb078_compact_fv_empty_0572)

theorem nb078_compact_fv_empty_0573 (g : Var) : (nb078_alpha_dummy_760 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1905 (g : Var) : (nb078_alpha_dummy_760 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_760, fv_syn_c1c] using (nb078_compact_fv_empty_0573 g)

theorem nb078_compact_fv_empty_0574 : (nb078_alpha_dummy_757) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1906 : (nb078_alpha_dummy_757) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_757, fv_syn_c1c] using (nb078_compact_fv_empty_0574)

theorem nb078_compact_fv_empty_0575 (g : Var) : (nb078_alpha_dummy_758 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1907 (g : Var) : (nb078_alpha_dummy_758 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_758, fv_syn_c1c] using (nb078_compact_fv_empty_0575 g)

theorem nb078_compact_envfresh_0255 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)), ((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_743) (nb078_alpha_dummy_746 g) (nb078_wpp_notmem_1848) (nb078_wpp_notmem_1849 g) (TEnvFresh.consFresh (nb078_alpha_dummy_742) (nb078_alpha_dummy_745 g) (nb078_wpp_notmem_1850) (nb078_wpp_notmem_1851 g) (TEnvFresh.consFresh (nb078_alpha_dummy_741) (nb078_alpha_dummy_744 g) (nb078_wpp_notmem_1852) (nb078_wpp_notmem_1853 g) (TEnvFresh.consFresh (nb078_alpha_dummy_739) (nb078_alpha_dummy_740 g) (nb078_wpp_notmem_1854) (nb078_wpp_notmem_1855 g) (TEnvFresh.consFresh (nb078_alpha_dummy_735) (nb078_alpha_dummy_737 g) (nb078_wpp_notmem_1856) (nb078_wpp_notmem_1857 g) (TEnvFresh.consFresh (nb078_alpha_dummy_736) (nb078_alpha_dummy_738 g) (nb078_wpp_notmem_1858) (nb078_wpp_notmem_1859 g) (TEnvFresh.consFresh (nb078_alpha_dummy_761) (nb078_alpha_dummy_762 g) (nb078_wpp_notmem_1902) (nb078_wpp_notmem_1903 g) (TEnvFresh.consFresh (nb078_alpha_dummy_759) (nb078_alpha_dummy_760 g) (nb078_wpp_notmem_1904) (nb078_wpp_notmem_1905 g) (TEnvFresh.consFresh (nb078_alpha_dummy_728) (nb078_alpha_dummy_730 g) (nb078_wpp_notmem_1860) (nb078_wpp_notmem_1861 g) (TEnvFresh.consFresh (nb078_alpha_dummy_727) (nb078_alpha_dummy_729 g) (nb078_wpp_notmem_1862) (nb078_wpp_notmem_1863 g) (TEnvFresh.consFresh (nb078_alpha_dummy_757) (nb078_alpha_dummy_758 g) (nb078_wpp_notmem_1906) (nb078_wpp_notmem_1907 g) (TEnvFresh.consFresh (nb078_alpha_dummy_731) (nb078_alpha_dummy_732 g) (nb078_wpp_notmem_1866) (nb078_wpp_notmem_1867 g) (TEnvFresh.consFresh (nb078_alpha_dummy_571) (nb078_alpha_dummy_574 g) (nb078_wpp_notmem_1590) (nb078_wpp_notmem_1591 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1468) (nb078_wpp_notmem_1469 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1470) (nb078_wpp_notmem_1471 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1472) (nb078_wpp_notmem_1473 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1474) (nb078_wpp_notmem_1475 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1476) (nb078_wpp_notmem_1477 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0255 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742), (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)), ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)), ((nb078_alpha_dummy_761), (nb078_alpha_dummy_762 g)), ((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)), ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)), ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0255 x y g)

theorem nb078_wpp_notmem_1908 : (nb078_alpha_dummy_761) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_761, fv_syn_c0] using (nb078_compact_fv_empty_0570)

theorem nb078_wpp_notmem_1909 (g : Var) : (nb078_alpha_dummy_762 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_762, fv_syn_c0] using (nb078_compact_fv_empty_0571 g)

theorem nb078_wpp_notmem_1910 : (nb078_alpha_dummy_759) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_759, fv_syn_c0] using (nb078_compact_fv_empty_0572)

theorem nb078_wpp_notmem_1911 (g : Var) : (nb078_alpha_dummy_760 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_760, fv_syn_c0] using (nb078_compact_fv_empty_0573 g)

theorem nb078_wpp_notmem_1912 : (nb078_alpha_dummy_757) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_757, fv_syn_c0] using (nb078_compact_fv_empty_0574)

theorem nb078_wpp_notmem_1913 (g : Var) : (nb078_alpha_dummy_758 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_758, fv_syn_c0] using (nb078_compact_fv_empty_0575 g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
