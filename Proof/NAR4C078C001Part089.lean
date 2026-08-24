import NAR4C078C001Part088

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

theorem nb078_compact_fv_empty_0436 : (nb078_alpha_dummy_585) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1456 : (nb078_alpha_dummy_585) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_585, fv_syn_c1c] using (nb078_compact_fv_empty_0436)

theorem nb078_compact_fv_empty_0437 (g : Var) : (nb078_alpha_dummy_587 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1457 (g : Var) : (nb078_alpha_dummy_587 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_587, fv_syn_c1c] using (nb078_compact_fv_empty_0437 g)

theorem nb078_compact_fv_empty_0438 : (nb078_alpha_dummy_586) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1458 : (nb078_alpha_dummy_586) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_586, fv_syn_c1c] using (nb078_compact_fv_empty_0438)

theorem nb078_compact_fv_empty_0439 (g : Var) : (nb078_alpha_dummy_588 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1459 (g : Var) : (nb078_alpha_dummy_588 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_588, fv_syn_c1c] using (nb078_compact_fv_empty_0439 g)

theorem nb078_compact_fv_empty_0440 : (nb078_alpha_dummy_578) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1460 : (nb078_alpha_dummy_578) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_578, fv_syn_c1c] using (nb078_compact_fv_empty_0440)

theorem nb078_compact_fv_empty_0441 (g : Var) : (nb078_alpha_dummy_580 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1461 (g : Var) : (nb078_alpha_dummy_580 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_580, fv_syn_c1c] using (nb078_compact_fv_empty_0441 g)

theorem nb078_compact_fv_empty_0442 : (nb078_alpha_dummy_577) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1462 : (nb078_alpha_dummy_577) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_577, fv_syn_c1c] using (nb078_compact_fv_empty_0442)

theorem nb078_compact_fv_empty_0443 (g : Var) : (nb078_alpha_dummy_579 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1463 (g : Var) : (nb078_alpha_dummy_579 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_579, fv_syn_c1c] using (nb078_compact_fv_empty_0443 g)

theorem nb078_compact_fv_empty_0444 : (nb078_alpha_dummy_583) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1464 : (nb078_alpha_dummy_583) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_583, fv_syn_c1c] using (nb078_compact_fv_empty_0444)

theorem nb078_compact_fv_empty_0445 (g : Var) : (nb078_alpha_dummy_584 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1465 (g : Var) : (nb078_alpha_dummy_584 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_584, fv_syn_c1c] using (nb078_compact_fv_empty_0445 g)

theorem nb078_compact_fv_empty_0446 : (nb078_alpha_dummy_581) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1466 : (nb078_alpha_dummy_581) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_581, fv_syn_c1c] using (nb078_compact_fv_empty_0446)

theorem nb078_compact_fv_empty_0447 (g : Var) : (nb078_alpha_dummy_582 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1467 (g : Var) : (nb078_alpha_dummy_582 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_582, fv_syn_c1c] using (nb078_compact_fv_empty_0447 g)

theorem nb078_compact_fv_empty_0448 : (nb078_alpha_dummy_570) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1468 : (nb078_alpha_dummy_570) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_570, fv_syn_c1c] using (nb078_compact_fv_empty_0448)

theorem nb078_compact_fv_empty_0449 (g : Var) : (nb078_alpha_dummy_573 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1469 (g : Var) : (nb078_alpha_dummy_573 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_573, fv_syn_c1c] using (nb078_compact_fv_empty_0449 g)

theorem nb078_compact_fv_empty_0450 : (nb078_alpha_dummy_569) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1470 : (nb078_alpha_dummy_569) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_569, fv_syn_c1c] using (nb078_compact_fv_empty_0450)

theorem nb078_compact_fv_empty_0451 (g : Var) : (nb078_alpha_dummy_572 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1471 (g : Var) : (nb078_alpha_dummy_572 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_572, fv_syn_c1c] using (nb078_compact_fv_empty_0451 g)

theorem nb078_compact_fv_empty_0452 : (nb078_alpha_dummy_575) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1472 : (nb078_alpha_dummy_575) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_575, fv_syn_c1c] using (nb078_compact_fv_empty_0452)

theorem nb078_compact_fv_empty_0453 (g : Var) : (nb078_alpha_dummy_576 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1473 (g : Var) : (nb078_alpha_dummy_576 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_576, fv_syn_c1c] using (nb078_compact_fv_empty_0453 g)

theorem nb078_compact_fv_empty_0454 : (nb078_alpha_dummy_567) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1474 : (nb078_alpha_dummy_567) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_567, fv_syn_c1c] using (nb078_compact_fv_empty_0454)

theorem nb078_compact_fv_empty_0455 (g : Var) : (nb078_alpha_dummy_568 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1475 (g : Var) : (nb078_alpha_dummy_568 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_568, fv_syn_c1c] using (nb078_compact_fv_empty_0455 g)

theorem nb078_compact_fv_empty_0456 : (nb078_alpha_dummy_565) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1476 : (nb078_alpha_dummy_565) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_565, fv_syn_c1c] using (nb078_compact_fv_empty_0456)

theorem nb078_compact_fv_empty_0457 (g : Var) : (nb078_alpha_dummy_566 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1477 (g : Var) : (nb078_alpha_dummy_566 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_566, fv_syn_c1c] using (nb078_compact_fv_empty_0457 g)

theorem nb078_compact_envfresh_0210 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_593) (nb078_alpha_dummy_596 g) (nb078_wpp_notmem_1448) (nb078_wpp_notmem_1449 g) (TEnvFresh.consFresh (nb078_alpha_dummy_592) (nb078_alpha_dummy_595 g) (nb078_wpp_notmem_1450) (nb078_wpp_notmem_1451 g) (TEnvFresh.consFresh (nb078_alpha_dummy_591) (nb078_alpha_dummy_594 g) (nb078_wpp_notmem_1452) (nb078_wpp_notmem_1453 g) (TEnvFresh.consFresh (nb078_alpha_dummy_589) (nb078_alpha_dummy_590 g) (nb078_wpp_notmem_1454) (nb078_wpp_notmem_1455 g) (TEnvFresh.consFresh (nb078_alpha_dummy_585) (nb078_alpha_dummy_587 g) (nb078_wpp_notmem_1456) (nb078_wpp_notmem_1457 g) (TEnvFresh.consFresh (nb078_alpha_dummy_586) (nb078_alpha_dummy_588 g) (nb078_wpp_notmem_1458) (nb078_wpp_notmem_1459 g) (TEnvFresh.consFresh (nb078_alpha_dummy_578) (nb078_alpha_dummy_580 g) (nb078_wpp_notmem_1460) (nb078_wpp_notmem_1461 g) (TEnvFresh.consFresh (nb078_alpha_dummy_577) (nb078_alpha_dummy_579 g) (nb078_wpp_notmem_1462) (nb078_wpp_notmem_1463 g) (TEnvFresh.consFresh (nb078_alpha_dummy_583) (nb078_alpha_dummy_584 g) (nb078_wpp_notmem_1464) (nb078_wpp_notmem_1465 g) (TEnvFresh.consFresh (nb078_alpha_dummy_581) (nb078_alpha_dummy_582 g) (nb078_wpp_notmem_1466) (nb078_wpp_notmem_1467 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1468) (nb078_wpp_notmem_1469 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1470) (nb078_wpp_notmem_1471 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1472) (nb078_wpp_notmem_1473 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1474) (nb078_wpp_notmem_1475 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1476) (nb078_wpp_notmem_1477 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb078_wpp_refl_0210 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0210 x y g)

theorem nb078_wpp_notmem_1478 : (nb078_alpha_dummy_593) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_593, fv_syn_c0] using (nb078_compact_fv_empty_0428)

theorem nb078_wpp_notmem_1479 (g : Var) : (nb078_alpha_dummy_596 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_596, fv_syn_c0] using (nb078_compact_fv_empty_0429 g)

theorem nb078_wpp_notmem_1480 : (nb078_alpha_dummy_592) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_592, fv_syn_c0] using (nb078_compact_fv_empty_0430)

theorem nb078_wpp_notmem_1481 (g : Var) : (nb078_alpha_dummy_595 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_595, fv_syn_c0] using (nb078_compact_fv_empty_0431 g)

theorem nb078_wpp_notmem_1482 : (nb078_alpha_dummy_591) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_591, fv_syn_c0] using (nb078_compact_fv_empty_0432)

theorem nb078_wpp_notmem_1483 (g : Var) : (nb078_alpha_dummy_594 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_594, fv_syn_c0] using (nb078_compact_fv_empty_0433 g)

theorem nb078_wpp_notmem_1484 : (nb078_alpha_dummy_589) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_589, fv_syn_c0] using (nb078_compact_fv_empty_0434)

theorem nb078_wpp_notmem_1485 (g : Var) : (nb078_alpha_dummy_590 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_590, fv_syn_c0] using (nb078_compact_fv_empty_0435 g)

theorem nb078_wpp_notmem_1486 : (nb078_alpha_dummy_585) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_585, fv_syn_c0] using (nb078_compact_fv_empty_0436)

theorem nb078_wpp_notmem_1487 (g : Var) : (nb078_alpha_dummy_587 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_587, fv_syn_c0] using (nb078_compact_fv_empty_0437 g)

theorem nb078_wpp_notmem_1488 : (nb078_alpha_dummy_586) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_586, fv_syn_c0] using (nb078_compact_fv_empty_0438)

theorem nb078_wpp_notmem_1489 (g : Var) : (nb078_alpha_dummy_588 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_588, fv_syn_c0] using (nb078_compact_fv_empty_0439 g)

theorem nb078_wpp_notmem_1490 : (nb078_alpha_dummy_578) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_578, fv_syn_c0] using (nb078_compact_fv_empty_0440)

theorem nb078_wpp_notmem_1491 (g : Var) : (nb078_alpha_dummy_580 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_580, fv_syn_c0] using (nb078_compact_fv_empty_0441 g)

theorem nb078_wpp_notmem_1492 : (nb078_alpha_dummy_577) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_577, fv_syn_c0] using (nb078_compact_fv_empty_0442)

theorem nb078_wpp_notmem_1493 (g : Var) : (nb078_alpha_dummy_579 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_579, fv_syn_c0] using (nb078_compact_fv_empty_0443 g)

theorem nb078_wpp_notmem_1494 : (nb078_alpha_dummy_583) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_583, fv_syn_c0] using (nb078_compact_fv_empty_0444)

theorem nb078_wpp_notmem_1495 (g : Var) : (nb078_alpha_dummy_584 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_584, fv_syn_c0] using (nb078_compact_fv_empty_0445 g)

theorem nb078_wpp_notmem_1496 : (nb078_alpha_dummy_581) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_581, fv_syn_c0] using (nb078_compact_fv_empty_0446)

theorem nb078_wpp_notmem_1497 (g : Var) : (nb078_alpha_dummy_582 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_582, fv_syn_c0] using (nb078_compact_fv_empty_0447 g)

theorem nb078_wpp_notmem_1498 : (nb078_alpha_dummy_570) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_570, fv_syn_c0] using (nb078_compact_fv_empty_0448)

theorem nb078_wpp_notmem_1499 (g : Var) : (nb078_alpha_dummy_573 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_573, fv_syn_c0] using (nb078_compact_fv_empty_0449 g)

theorem nb078_wpp_notmem_1500 : (nb078_alpha_dummy_569) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_569, fv_syn_c0] using (nb078_compact_fv_empty_0450)

theorem nb078_wpp_notmem_1501 (g : Var) : (nb078_alpha_dummy_572 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_572, fv_syn_c0] using (nb078_compact_fv_empty_0451 g)

theorem nb078_wpp_notmem_1502 : (nb078_alpha_dummy_575) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_575, fv_syn_c0] using (nb078_compact_fv_empty_0452)

theorem nb078_wpp_notmem_1503 (g : Var) : (nb078_alpha_dummy_576 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_576, fv_syn_c0] using (nb078_compact_fv_empty_0453 g)

theorem nb078_wpp_notmem_1504 : (nb078_alpha_dummy_567) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_567, fv_syn_c0] using (nb078_compact_fv_empty_0454)

theorem nb078_wpp_notmem_1505 (g : Var) : (nb078_alpha_dummy_568 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_568, fv_syn_c0] using (nb078_compact_fv_empty_0455 g)

theorem nb078_wpp_notmem_1506 : (nb078_alpha_dummy_565) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_565, fv_syn_c0] using (nb078_compact_fv_empty_0456)

theorem nb078_wpp_notmem_1507 (g : Var) : (nb078_alpha_dummy_566 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_566, fv_syn_c0] using (nb078_compact_fv_empty_0457 g)

theorem nb078_compact_envfresh_0211 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_593) (nb078_alpha_dummy_596 g) (nb078_wpp_notmem_1478) (nb078_wpp_notmem_1479 g) (TEnvFresh.consFresh (nb078_alpha_dummy_592) (nb078_alpha_dummy_595 g) (nb078_wpp_notmem_1480) (nb078_wpp_notmem_1481 g) (TEnvFresh.consFresh (nb078_alpha_dummy_591) (nb078_alpha_dummy_594 g) (nb078_wpp_notmem_1482) (nb078_wpp_notmem_1483 g) (TEnvFresh.consFresh (nb078_alpha_dummy_589) (nb078_alpha_dummy_590 g) (nb078_wpp_notmem_1484) (nb078_wpp_notmem_1485 g) (TEnvFresh.consFresh (nb078_alpha_dummy_585) (nb078_alpha_dummy_587 g) (nb078_wpp_notmem_1486) (nb078_wpp_notmem_1487 g) (TEnvFresh.consFresh (nb078_alpha_dummy_586) (nb078_alpha_dummy_588 g) (nb078_wpp_notmem_1488) (nb078_wpp_notmem_1489 g) (TEnvFresh.consFresh (nb078_alpha_dummy_578) (nb078_alpha_dummy_580 g) (nb078_wpp_notmem_1490) (nb078_wpp_notmem_1491 g) (TEnvFresh.consFresh (nb078_alpha_dummy_577) (nb078_alpha_dummy_579 g) (nb078_wpp_notmem_1492) (nb078_wpp_notmem_1493 g) (TEnvFresh.consFresh (nb078_alpha_dummy_583) (nb078_alpha_dummy_584 g) (nb078_wpp_notmem_1494) (nb078_wpp_notmem_1495 g) (TEnvFresh.consFresh (nb078_alpha_dummy_581) (nb078_alpha_dummy_582 g) (nb078_wpp_notmem_1496) (nb078_wpp_notmem_1497 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1498) (nb078_wpp_notmem_1499 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1500) (nb078_wpp_notmem_1501 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1502) (nb078_wpp_notmem_1503 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1504) (nb078_wpp_notmem_1505 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1506) (nb078_wpp_notmem_1507 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0788) (nb078_wpp_notmem_0789 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb078_wpp_refl_0211 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0211 x y g)

theorem nb078_wpp_notmem_1508 : (nb078_alpha_dummy_589) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_589, fv_syn_cnnc] using (nb078_compact_fv_empty_0434)

theorem nb078_wpp_notmem_1509 (g : Var) : (nb078_alpha_dummy_590 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_590, fv_syn_cnnc] using (nb078_compact_fv_empty_0435 g)

theorem nb078_wpp_notmem_1510 : (nb078_alpha_dummy_585) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_585, fv_syn_cnnc] using (nb078_compact_fv_empty_0436)

theorem nb078_wpp_notmem_1511 (g : Var) : (nb078_alpha_dummy_587 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_587, fv_syn_cnnc] using (nb078_compact_fv_empty_0437 g)

theorem nb078_wpp_notmem_1512 : (nb078_alpha_dummy_586) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_586, fv_syn_cnnc] using (nb078_compact_fv_empty_0438)

theorem nb078_wpp_notmem_1513 (g : Var) : (nb078_alpha_dummy_588 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_588, fv_syn_cnnc] using (nb078_compact_fv_empty_0439 g)

theorem nb078_wpp_notmem_1514 : (nb078_alpha_dummy_578) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_578, fv_syn_cnnc] using (nb078_compact_fv_empty_0440)

theorem nb078_wpp_notmem_1515 (g : Var) : (nb078_alpha_dummy_580 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_580, fv_syn_cnnc] using (nb078_compact_fv_empty_0441 g)

theorem nb078_wpp_notmem_1516 : (nb078_alpha_dummy_577) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_577, fv_syn_cnnc] using (nb078_compact_fv_empty_0442)

theorem nb078_wpp_notmem_1517 (g : Var) : (nb078_alpha_dummy_579 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_579, fv_syn_cnnc] using (nb078_compact_fv_empty_0443 g)

theorem nb078_wpp_notmem_1518 : (nb078_alpha_dummy_583) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_583, fv_syn_cnnc] using (nb078_compact_fv_empty_0444)

theorem nb078_wpp_notmem_1519 (g : Var) : (nb078_alpha_dummy_584 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_584, fv_syn_cnnc] using (nb078_compact_fv_empty_0445 g)

theorem nb078_wpp_notmem_1520 : (nb078_alpha_dummy_581) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_581, fv_syn_cnnc] using (nb078_compact_fv_empty_0446)

theorem nb078_wpp_notmem_1521 (g : Var) : (nb078_alpha_dummy_582 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_582, fv_syn_cnnc] using (nb078_compact_fv_empty_0447 g)

theorem nb078_wpp_notmem_1522 : (nb078_alpha_dummy_570) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_570, fv_syn_cnnc] using (nb078_compact_fv_empty_0448)

theorem nb078_wpp_notmem_1523 (g : Var) : (nb078_alpha_dummy_573 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_573, fv_syn_cnnc] using (nb078_compact_fv_empty_0449 g)

theorem nb078_wpp_notmem_1524 : (nb078_alpha_dummy_569) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_569, fv_syn_cnnc] using (nb078_compact_fv_empty_0450)

theorem nb078_wpp_notmem_1525 (g : Var) : (nb078_alpha_dummy_572 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_572, fv_syn_cnnc] using (nb078_compact_fv_empty_0451 g)

theorem nb078_wpp_notmem_1526 : (nb078_alpha_dummy_575) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_575, fv_syn_cnnc] using (nb078_compact_fv_empty_0452)

theorem nb078_wpp_notmem_1527 (g : Var) : (nb078_alpha_dummy_576 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_576, fv_syn_cnnc] using (nb078_compact_fv_empty_0453 g)

theorem nb078_wpp_notmem_1528 : (nb078_alpha_dummy_567) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_567, fv_syn_cnnc] using (nb078_compact_fv_empty_0454)

theorem nb078_wpp_notmem_1529 (g : Var) : (nb078_alpha_dummy_568 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_568, fv_syn_cnnc] using (nb078_compact_fv_empty_0455 g)

theorem nb078_wpp_notmem_1530 : (nb078_alpha_dummy_565) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_565, fv_syn_cnnc] using (nb078_compact_fv_empty_0456)

theorem nb078_wpp_notmem_1531 (g : Var) : (nb078_alpha_dummy_566 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_566, fv_syn_cnnc] using (nb078_compact_fv_empty_0457 g)

theorem nb078_compact_envfresh_0212 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_589) (nb078_alpha_dummy_590 g) (nb078_wpp_notmem_1508) (nb078_wpp_notmem_1509 g) (TEnvFresh.consFresh (nb078_alpha_dummy_585) (nb078_alpha_dummy_587 g) (nb078_wpp_notmem_1510) (nb078_wpp_notmem_1511 g) (TEnvFresh.consFresh (nb078_alpha_dummy_586) (nb078_alpha_dummy_588 g) (nb078_wpp_notmem_1512) (nb078_wpp_notmem_1513 g) (TEnvFresh.consFresh (nb078_alpha_dummy_578) (nb078_alpha_dummy_580 g) (nb078_wpp_notmem_1514) (nb078_wpp_notmem_1515 g) (TEnvFresh.consFresh (nb078_alpha_dummy_577) (nb078_alpha_dummy_579 g) (nb078_wpp_notmem_1516) (nb078_wpp_notmem_1517 g) (TEnvFresh.consFresh (nb078_alpha_dummy_583) (nb078_alpha_dummy_584 g) (nb078_wpp_notmem_1518) (nb078_wpp_notmem_1519 g) (TEnvFresh.consFresh (nb078_alpha_dummy_581) (nb078_alpha_dummy_582 g) (nb078_wpp_notmem_1520) (nb078_wpp_notmem_1521 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1522) (nb078_wpp_notmem_1523 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1524) (nb078_wpp_notmem_1525 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1526) (nb078_wpp_notmem_1527 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1528) (nb078_wpp_notmem_1529 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1530) (nb078_wpp_notmem_1531 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0814) (nb078_wpp_notmem_0815 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0212 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0212 x y g)

noncomputable def nb078_split_alpha_0062 (x : Var) (y : Var) (g : Var) : TAlphaWff [((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_583)) (Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_583)) (Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_584 g)) (Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_584 g)) (Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0596) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0597 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0593) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0595 g) 0)) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0598) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0599 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0598) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0599 g) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_578))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_580 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0602) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0603 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0602) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0603 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0210 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0606) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0607 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0604) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0605 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0610) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0611 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0608) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0609 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0606) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0607 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0604) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0605 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0610) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0611 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0608) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0609 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0211 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0614) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0615 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0612) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0613 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0614) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0615 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0612) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0613 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0618) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0619 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0616) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0617 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0618) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0619 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0616) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0617 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0212 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0212 x y g)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0596) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0597 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0593) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0595 g) 0)) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv) (by decide)) (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0598) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0599 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0598) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0599 g) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_578))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_580 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0602) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0603 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0602) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0603 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0210 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0606) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0607 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0604) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0605 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0610) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0611 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0608) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0609 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0606) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0607 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0604) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0605 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0610) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0611 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0608) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0609 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0211 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0614) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0615 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0612) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0613 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0614) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0615 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0612) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0613 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0618) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0619 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0616) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0617 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0618) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0619 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0616) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0617 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0212 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0212 x y g))))))))))))))))))))))))))))

theorem nb078_compact_fv_empty_0458 : (nb078_alpha_dummy_611) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1532 : (nb078_alpha_dummy_611) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_611, fv_syn_c1c] using (nb078_compact_fv_empty_0458)

theorem nb078_compact_fv_empty_0459 (g : Var) : (nb078_alpha_dummy_612 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1533 (g : Var) : (nb078_alpha_dummy_612 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_612, fv_syn_c1c] using (nb078_compact_fv_empty_0459 g)

theorem nb078_compact_fv_empty_0460 : (nb078_alpha_dummy_609) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1534 : (nb078_alpha_dummy_609) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_609, fv_syn_c1c] using (nb078_compact_fv_empty_0460)

theorem nb078_compact_fv_empty_0461 (g : Var) : (nb078_alpha_dummy_610 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1535 (g : Var) : (nb078_alpha_dummy_610 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_610, fv_syn_c1c] using (nb078_compact_fv_empty_0461 g)

theorem nb078_compact_fv_empty_0462 : (nb078_alpha_dummy_607) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1536 : (nb078_alpha_dummy_607) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_607, fv_syn_c1c] using (nb078_compact_fv_empty_0462)

theorem nb078_compact_fv_empty_0463 (g : Var) : (nb078_alpha_dummy_608 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1537 (g : Var) : (nb078_alpha_dummy_608 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_608, fv_syn_c1c] using (nb078_compact_fv_empty_0463 g)

theorem nb078_compact_envfresh_0213 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_593) (nb078_alpha_dummy_596 g) (nb078_wpp_notmem_1448) (nb078_wpp_notmem_1449 g) (TEnvFresh.consFresh (nb078_alpha_dummy_592) (nb078_alpha_dummy_595 g) (nb078_wpp_notmem_1450) (nb078_wpp_notmem_1451 g) (TEnvFresh.consFresh (nb078_alpha_dummy_591) (nb078_alpha_dummy_594 g) (nb078_wpp_notmem_1452) (nb078_wpp_notmem_1453 g) (TEnvFresh.consFresh (nb078_alpha_dummy_589) (nb078_alpha_dummy_590 g) (nb078_wpp_notmem_1454) (nb078_wpp_notmem_1455 g) (TEnvFresh.consFresh (nb078_alpha_dummy_585) (nb078_alpha_dummy_587 g) (nb078_wpp_notmem_1456) (nb078_wpp_notmem_1457 g) (TEnvFresh.consFresh (nb078_alpha_dummy_586) (nb078_alpha_dummy_588 g) (nb078_wpp_notmem_1458) (nb078_wpp_notmem_1459 g) (TEnvFresh.consFresh (nb078_alpha_dummy_611) (nb078_alpha_dummy_612 g) (nb078_wpp_notmem_1532) (nb078_wpp_notmem_1533 g) (TEnvFresh.consFresh (nb078_alpha_dummy_609) (nb078_alpha_dummy_610 g) (nb078_wpp_notmem_1534) (nb078_wpp_notmem_1535 g) (TEnvFresh.consFresh (nb078_alpha_dummy_578) (nb078_alpha_dummy_580 g) (nb078_wpp_notmem_1460) (nb078_wpp_notmem_1461 g) (TEnvFresh.consFresh (nb078_alpha_dummy_577) (nb078_alpha_dummy_579 g) (nb078_wpp_notmem_1462) (nb078_wpp_notmem_1463 g) (TEnvFresh.consFresh (nb078_alpha_dummy_607) (nb078_alpha_dummy_608 g) (nb078_wpp_notmem_1536) (nb078_wpp_notmem_1537 g) (TEnvFresh.consFresh (nb078_alpha_dummy_581) (nb078_alpha_dummy_582 g) (nb078_wpp_notmem_1466) (nb078_wpp_notmem_1467 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1468) (nb078_wpp_notmem_1469 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1470) (nb078_wpp_notmem_1471 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1472) (nb078_wpp_notmem_1473 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1474) (nb078_wpp_notmem_1475 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1476) (nb078_wpp_notmem_1477 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
