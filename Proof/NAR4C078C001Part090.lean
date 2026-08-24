import NAR4C078C001Part089

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

noncomputable def nb078_wpp_refl_0213 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0213 x y g)

theorem nb078_wpp_notmem_1538 : (nb078_alpha_dummy_611) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_611, fv_syn_c0] using (nb078_compact_fv_empty_0458)

theorem nb078_wpp_notmem_1539 (g : Var) : (nb078_alpha_dummy_612 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_612, fv_syn_c0] using (nb078_compact_fv_empty_0459 g)

theorem nb078_wpp_notmem_1540 : (nb078_alpha_dummy_609) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_609, fv_syn_c0] using (nb078_compact_fv_empty_0460)

theorem nb078_wpp_notmem_1541 (g : Var) : (nb078_alpha_dummy_610 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_610, fv_syn_c0] using (nb078_compact_fv_empty_0461 g)

theorem nb078_wpp_notmem_1542 : (nb078_alpha_dummy_607) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_607, fv_syn_c0] using (nb078_compact_fv_empty_0462)

theorem nb078_wpp_notmem_1543 (g : Var) : (nb078_alpha_dummy_608 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_608, fv_syn_c0] using (nb078_compact_fv_empty_0463 g)

theorem nb078_compact_envfresh_0214 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_593) (nb078_alpha_dummy_596 g) (nb078_wpp_notmem_1478) (nb078_wpp_notmem_1479 g) (TEnvFresh.consFresh (nb078_alpha_dummy_592) (nb078_alpha_dummy_595 g) (nb078_wpp_notmem_1480) (nb078_wpp_notmem_1481 g) (TEnvFresh.consFresh (nb078_alpha_dummy_591) (nb078_alpha_dummy_594 g) (nb078_wpp_notmem_1482) (nb078_wpp_notmem_1483 g) (TEnvFresh.consFresh (nb078_alpha_dummy_589) (nb078_alpha_dummy_590 g) (nb078_wpp_notmem_1484) (nb078_wpp_notmem_1485 g) (TEnvFresh.consFresh (nb078_alpha_dummy_585) (nb078_alpha_dummy_587 g) (nb078_wpp_notmem_1486) (nb078_wpp_notmem_1487 g) (TEnvFresh.consFresh (nb078_alpha_dummy_586) (nb078_alpha_dummy_588 g) (nb078_wpp_notmem_1488) (nb078_wpp_notmem_1489 g) (TEnvFresh.consFresh (nb078_alpha_dummy_611) (nb078_alpha_dummy_612 g) (nb078_wpp_notmem_1538) (nb078_wpp_notmem_1539 g) (TEnvFresh.consFresh (nb078_alpha_dummy_609) (nb078_alpha_dummy_610 g) (nb078_wpp_notmem_1540) (nb078_wpp_notmem_1541 g) (TEnvFresh.consFresh (nb078_alpha_dummy_578) (nb078_alpha_dummy_580 g) (nb078_wpp_notmem_1490) (nb078_wpp_notmem_1491 g) (TEnvFresh.consFresh (nb078_alpha_dummy_577) (nb078_alpha_dummy_579 g) (nb078_wpp_notmem_1492) (nb078_wpp_notmem_1493 g) (TEnvFresh.consFresh (nb078_alpha_dummy_607) (nb078_alpha_dummy_608 g) (nb078_wpp_notmem_1542) (nb078_wpp_notmem_1543 g) (TEnvFresh.consFresh (nb078_alpha_dummy_581) (nb078_alpha_dummy_582 g) (nb078_wpp_notmem_1496) (nb078_wpp_notmem_1497 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1498) (nb078_wpp_notmem_1499 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1500) (nb078_wpp_notmem_1501 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1502) (nb078_wpp_notmem_1503 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1504) (nb078_wpp_notmem_1505 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1506) (nb078_wpp_notmem_1507 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0788) (nb078_wpp_notmem_0789 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb078_wpp_refl_0214 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0214 x y g)

theorem nb078_wpp_notmem_1544 : (nb078_alpha_dummy_611) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_611, fv_syn_cnnc] using (nb078_compact_fv_empty_0458)

theorem nb078_wpp_notmem_1545 (g : Var) : (nb078_alpha_dummy_612 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_612, fv_syn_cnnc] using (nb078_compact_fv_empty_0459 g)

theorem nb078_wpp_notmem_1546 : (nb078_alpha_dummy_609) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_609, fv_syn_cnnc] using (nb078_compact_fv_empty_0460)

theorem nb078_wpp_notmem_1547 (g : Var) : (nb078_alpha_dummy_610 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_610, fv_syn_cnnc] using (nb078_compact_fv_empty_0461 g)

theorem nb078_wpp_notmem_1548 : (nb078_alpha_dummy_607) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_607, fv_syn_cnnc] using (nb078_compact_fv_empty_0462)

theorem nb078_wpp_notmem_1549 (g : Var) : (nb078_alpha_dummy_608 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_608, fv_syn_cnnc] using (nb078_compact_fv_empty_0463 g)

theorem nb078_compact_envfresh_0215 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_589) (nb078_alpha_dummy_590 g) (nb078_wpp_notmem_1508) (nb078_wpp_notmem_1509 g) (TEnvFresh.consFresh (nb078_alpha_dummy_585) (nb078_alpha_dummy_587 g) (nb078_wpp_notmem_1510) (nb078_wpp_notmem_1511 g) (TEnvFresh.consFresh (nb078_alpha_dummy_586) (nb078_alpha_dummy_588 g) (nb078_wpp_notmem_1512) (nb078_wpp_notmem_1513 g) (TEnvFresh.consFresh (nb078_alpha_dummy_611) (nb078_alpha_dummy_612 g) (nb078_wpp_notmem_1544) (nb078_wpp_notmem_1545 g) (TEnvFresh.consFresh (nb078_alpha_dummy_609) (nb078_alpha_dummy_610 g) (nb078_wpp_notmem_1546) (nb078_wpp_notmem_1547 g) (TEnvFresh.consFresh (nb078_alpha_dummy_578) (nb078_alpha_dummy_580 g) (nb078_wpp_notmem_1514) (nb078_wpp_notmem_1515 g) (TEnvFresh.consFresh (nb078_alpha_dummy_577) (nb078_alpha_dummy_579 g) (nb078_wpp_notmem_1516) (nb078_wpp_notmem_1517 g) (TEnvFresh.consFresh (nb078_alpha_dummy_607) (nb078_alpha_dummy_608 g) (nb078_wpp_notmem_1548) (nb078_wpp_notmem_1549 g) (TEnvFresh.consFresh (nb078_alpha_dummy_581) (nb078_alpha_dummy_582 g) (nb078_wpp_notmem_1520) (nb078_wpp_notmem_1521 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1522) (nb078_wpp_notmem_1523 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1524) (nb078_wpp_notmem_1525 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1526) (nb078_wpp_notmem_1527 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1528) (nb078_wpp_notmem_1529 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1530) (nb078_wpp_notmem_1531 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0814) (nb078_wpp_notmem_0815 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0215 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0215 x y g)

theorem nb078_wpp_notmem_1550 : (nb078_alpha_dummy_609) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_609, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0460)

theorem nb078_wpp_notmem_1551 (g : Var) : (nb078_alpha_dummy_610 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_610, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0461 g)

theorem nb078_wpp_notmem_1552 : (nb078_alpha_dummy_578) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_578, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0440)

theorem nb078_wpp_notmem_1553 (g : Var) : (nb078_alpha_dummy_580 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_580, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0441 g)

theorem nb078_wpp_notmem_1554 : (nb078_alpha_dummy_577) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_577, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0442)

theorem nb078_wpp_notmem_1555 (g : Var) : (nb078_alpha_dummy_579 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_579, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0443 g)

theorem nb078_wpp_notmem_1556 : (nb078_alpha_dummy_607) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_607, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0462)

theorem nb078_wpp_notmem_1557 (g : Var) : (nb078_alpha_dummy_608 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_608, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0463 g)

theorem nb078_wpp_notmem_1558 : (nb078_alpha_dummy_581) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_581, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0446)

theorem nb078_wpp_notmem_1559 (g : Var) : (nb078_alpha_dummy_582 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_582, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0447 g)

theorem nb078_wpp_notmem_1560 : (nb078_alpha_dummy_570) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_570, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0448)

theorem nb078_wpp_notmem_1561 (g : Var) : (nb078_alpha_dummy_573 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_573, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0449 g)

theorem nb078_wpp_notmem_1562 : (nb078_alpha_dummy_569) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_569, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0450)

theorem nb078_wpp_notmem_1563 (g : Var) : (nb078_alpha_dummy_572 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_572, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0451 g)

theorem nb078_wpp_notmem_1564 : (nb078_alpha_dummy_575) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_575, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0452)

theorem nb078_wpp_notmem_1565 (g : Var) : (nb078_alpha_dummy_576 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_576, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0453 g)

theorem nb078_wpp_notmem_1566 : (nb078_alpha_dummy_567) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_567, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0454)

theorem nb078_wpp_notmem_1567 (g : Var) : (nb078_alpha_dummy_568 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_568, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0455 g)

theorem nb078_wpp_notmem_1568 : (nb078_alpha_dummy_565) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_565, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0456)

theorem nb078_wpp_notmem_1569 (g : Var) : (nb078_alpha_dummy_566 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_566, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0457 g)

theorem nb078_compact_envfresh_0216 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_609) (nb078_alpha_dummy_610 g) (nb078_wpp_notmem_1550) (nb078_wpp_notmem_1551 g) (TEnvFresh.consFresh (nb078_alpha_dummy_578) (nb078_alpha_dummy_580 g) (nb078_wpp_notmem_1552) (nb078_wpp_notmem_1553 g) (TEnvFresh.consFresh (nb078_alpha_dummy_577) (nb078_alpha_dummy_579 g) (nb078_wpp_notmem_1554) (nb078_wpp_notmem_1555 g) (TEnvFresh.consFresh (nb078_alpha_dummy_607) (nb078_alpha_dummy_608 g) (nb078_wpp_notmem_1556) (nb078_wpp_notmem_1557 g) (TEnvFresh.consFresh (nb078_alpha_dummy_581) (nb078_alpha_dummy_582 g) (nb078_wpp_notmem_1558) (nb078_wpp_notmem_1559 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1560) (nb078_wpp_notmem_1561 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1562) (nb078_wpp_notmem_1563 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1564) (nb078_wpp_notmem_1565 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1566) (nb078_wpp_notmem_1567 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1568) (nb078_wpp_notmem_1569 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0854) (nb078_wpp_notmem_0855 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))

noncomputable def nb078_wpp_refl_0216 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0216 x y g)

noncomputable def nb078_split_alpha_0063 (x : Var) (y : Var) (g : Var) : TAlphaWff [((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_609)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_578))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_609)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_610 g)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_610 g)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0598) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0599 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0598) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0599 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0628) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0629 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0626) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0627 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_578))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_580 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0602) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0603 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0602) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0603 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0213 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0606) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0607 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0604) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0605 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0610) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0611 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0608) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0609 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0606) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0607 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0604) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0605 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0610) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0611 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0608) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0609 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0214 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0614) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0615 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0612) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0613 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0614) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0615 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0612) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0613 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0618) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0619 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0616) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0617 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0618) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0619 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0616) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0617 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0215 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0215 x y g)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0598) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0599 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0598) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0599 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0628) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0629 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0626) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0627 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_578))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_580 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0602) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0603 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0602) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0603 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0213 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0606) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0607 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0604) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0605 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0610) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0611 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0608) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0609 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0606) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0607 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0604) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0605 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0610) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0611 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0608) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0609 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592), (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)), ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0214 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0614) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0615 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0612) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0613 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0614) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0615 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0612) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0613 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0618) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0619 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0616) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0617 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0618) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0619 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0616) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0617 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0215 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0600) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0601 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0215 x y g)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (nb078_wpp_refl_0216 x y g)))))

theorem nb078_compact_fv_empty_0464 : (nb078_alpha_dummy_629) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1570 : (nb078_alpha_dummy_629) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_629, fv_syn_c1c] using (nb078_compact_fv_empty_0464)

theorem nb078_compact_fv_empty_0465 (g : Var) : (nb078_alpha_dummy_632 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1571 (g : Var) : (nb078_alpha_dummy_632 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_632, fv_syn_c1c] using (nb078_compact_fv_empty_0465 g)

theorem nb078_compact_fv_empty_0466 : (nb078_alpha_dummy_628) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1572 : (nb078_alpha_dummy_628) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_628, fv_syn_c1c] using (nb078_compact_fv_empty_0466)

theorem nb078_compact_fv_empty_0467 (g : Var) : (nb078_alpha_dummy_631 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1573 (g : Var) : (nb078_alpha_dummy_631 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_631, fv_syn_c1c] using (nb078_compact_fv_empty_0467 g)

theorem nb078_compact_fv_empty_0468 : (nb078_alpha_dummy_627) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1574 : (nb078_alpha_dummy_627) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_627, fv_syn_c1c] using (nb078_compact_fv_empty_0468)

theorem nb078_compact_fv_empty_0469 (g : Var) : (nb078_alpha_dummy_630 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1575 (g : Var) : (nb078_alpha_dummy_630 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_630, fv_syn_c1c] using (nb078_compact_fv_empty_0469 g)

theorem nb078_compact_fv_empty_0470 : (nb078_alpha_dummy_625) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1576 : (nb078_alpha_dummy_625) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_625, fv_syn_c1c] using (nb078_compact_fv_empty_0470)

theorem nb078_compact_fv_empty_0471 (g : Var) : (nb078_alpha_dummy_626 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1577 (g : Var) : (nb078_alpha_dummy_626 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_626, fv_syn_c1c] using (nb078_compact_fv_empty_0471 g)

theorem nb078_compact_fv_empty_0472 : (nb078_alpha_dummy_621) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1578 : (nb078_alpha_dummy_621) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_621, fv_syn_c1c] using (nb078_compact_fv_empty_0472)

theorem nb078_compact_fv_empty_0473 (g : Var) : (nb078_alpha_dummy_623 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1579 (g : Var) : (nb078_alpha_dummy_623 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_623, fv_syn_c1c] using (nb078_compact_fv_empty_0473 g)

theorem nb078_compact_fv_empty_0474 : (nb078_alpha_dummy_622) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1580 : (nb078_alpha_dummy_622) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_622, fv_syn_c1c] using (nb078_compact_fv_empty_0474)

theorem nb078_compact_fv_empty_0475 (g : Var) : (nb078_alpha_dummy_624 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1581 (g : Var) : (nb078_alpha_dummy_624 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_624, fv_syn_c1c] using (nb078_compact_fv_empty_0475 g)

theorem nb078_compact_fv_empty_0476 : (nb078_alpha_dummy_614) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1582 : (nb078_alpha_dummy_614) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_614, fv_syn_c1c] using (nb078_compact_fv_empty_0476)

theorem nb078_compact_fv_empty_0477 (g : Var) : (nb078_alpha_dummy_616 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1583 (g : Var) : (nb078_alpha_dummy_616 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_616, fv_syn_c1c] using (nb078_compact_fv_empty_0477 g)

theorem nb078_compact_fv_empty_0478 : (nb078_alpha_dummy_613) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1584 : (nb078_alpha_dummy_613) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_613, fv_syn_c1c] using (nb078_compact_fv_empty_0478)

theorem nb078_compact_fv_empty_0479 (g : Var) : (nb078_alpha_dummy_615 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1585 (g : Var) : (nb078_alpha_dummy_615 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_615, fv_syn_c1c] using (nb078_compact_fv_empty_0479 g)

theorem nb078_compact_fv_empty_0480 : (nb078_alpha_dummy_619) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1586 : (nb078_alpha_dummy_619) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_619, fv_syn_c1c] using (nb078_compact_fv_empty_0480)

theorem nb078_compact_fv_empty_0481 (g : Var) : (nb078_alpha_dummy_620 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1587 (g : Var) : (nb078_alpha_dummy_620 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_620, fv_syn_c1c] using (nb078_compact_fv_empty_0481 g)

theorem nb078_compact_fv_empty_0482 : (nb078_alpha_dummy_617) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1588 : (nb078_alpha_dummy_617) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_617, fv_syn_c1c] using (nb078_compact_fv_empty_0482)

theorem nb078_compact_fv_empty_0483 (g : Var) : (nb078_alpha_dummy_618 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1589 (g : Var) : (nb078_alpha_dummy_618 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_618, fv_syn_c1c] using (nb078_compact_fv_empty_0483 g)

theorem nb078_compact_fv_empty_0484 : (nb078_alpha_dummy_571) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1590 : (nb078_alpha_dummy_571) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_571, fv_syn_c1c] using (nb078_compact_fv_empty_0484)

theorem nb078_compact_fv_empty_0485 (g : Var) : (nb078_alpha_dummy_574 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1591 (g : Var) : (nb078_alpha_dummy_574 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_574, fv_syn_c1c] using (nb078_compact_fv_empty_0485 g)

theorem nb078_compact_envfresh_0217 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628), (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)), ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_629) (nb078_alpha_dummy_632 g) (nb078_wpp_notmem_1570) (nb078_wpp_notmem_1571 g) (TEnvFresh.consFresh (nb078_alpha_dummy_628) (nb078_alpha_dummy_631 g) (nb078_wpp_notmem_1572) (nb078_wpp_notmem_1573 g) (TEnvFresh.consFresh (nb078_alpha_dummy_627) (nb078_alpha_dummy_630 g) (nb078_wpp_notmem_1574) (nb078_wpp_notmem_1575 g) (TEnvFresh.consFresh (nb078_alpha_dummy_625) (nb078_alpha_dummy_626 g) (nb078_wpp_notmem_1576) (nb078_wpp_notmem_1577 g) (TEnvFresh.consFresh (nb078_alpha_dummy_621) (nb078_alpha_dummy_623 g) (nb078_wpp_notmem_1578) (nb078_wpp_notmem_1579 g) (TEnvFresh.consFresh (nb078_alpha_dummy_622) (nb078_alpha_dummy_624 g) (nb078_wpp_notmem_1580) (nb078_wpp_notmem_1581 g) (TEnvFresh.consFresh (nb078_alpha_dummy_614) (nb078_alpha_dummy_616 g) (nb078_wpp_notmem_1582) (nb078_wpp_notmem_1583 g) (TEnvFresh.consFresh (nb078_alpha_dummy_613) (nb078_alpha_dummy_615 g) (nb078_wpp_notmem_1584) (nb078_wpp_notmem_1585 g) (TEnvFresh.consFresh (nb078_alpha_dummy_619) (nb078_alpha_dummy_620 g) (nb078_wpp_notmem_1586) (nb078_wpp_notmem_1587 g) (TEnvFresh.consFresh (nb078_alpha_dummy_617) (nb078_alpha_dummy_618 g) (nb078_wpp_notmem_1588) (nb078_wpp_notmem_1589 g) (TEnvFresh.consFresh (nb078_alpha_dummy_571) (nb078_alpha_dummy_574 g) (nb078_wpp_notmem_1590) (nb078_wpp_notmem_1591 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1468) (nb078_wpp_notmem_1469 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1470) (nb078_wpp_notmem_1471 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1472) (nb078_wpp_notmem_1473 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1474) (nb078_wpp_notmem_1475 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1476) (nb078_wpp_notmem_1477 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0217 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628), (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)), ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0217 x y g)

theorem nb078_wpp_notmem_1592 : (nb078_alpha_dummy_629) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_629, fv_syn_c0] using (nb078_compact_fv_empty_0464)

theorem nb078_wpp_notmem_1593 (g : Var) : (nb078_alpha_dummy_632 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_632, fv_syn_c0] using (nb078_compact_fv_empty_0465 g)

theorem nb078_wpp_notmem_1594 : (nb078_alpha_dummy_628) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_628, fv_syn_c0] using (nb078_compact_fv_empty_0466)

theorem nb078_wpp_notmem_1595 (g : Var) : (nb078_alpha_dummy_631 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_631, fv_syn_c0] using (nb078_compact_fv_empty_0467 g)

theorem nb078_wpp_notmem_1596 : (nb078_alpha_dummy_627) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_627, fv_syn_c0] using (nb078_compact_fv_empty_0468)

theorem nb078_wpp_notmem_1597 (g : Var) : (nb078_alpha_dummy_630 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_630, fv_syn_c0] using (nb078_compact_fv_empty_0469 g)

theorem nb078_wpp_notmem_1598 : (nb078_alpha_dummy_625) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_625, fv_syn_c0] using (nb078_compact_fv_empty_0470)

theorem nb078_wpp_notmem_1599 (g : Var) : (nb078_alpha_dummy_626 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_626, fv_syn_c0] using (nb078_compact_fv_empty_0471 g)

theorem nb078_wpp_notmem_1600 : (nb078_alpha_dummy_621) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_621, fv_syn_c0] using (nb078_compact_fv_empty_0472)

theorem nb078_wpp_notmem_1601 (g : Var) : (nb078_alpha_dummy_623 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_623, fv_syn_c0] using (nb078_compact_fv_empty_0473 g)

theorem nb078_wpp_notmem_1602 : (nb078_alpha_dummy_622) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_622, fv_syn_c0] using (nb078_compact_fv_empty_0474)

theorem nb078_wpp_notmem_1603 (g : Var) : (nb078_alpha_dummy_624 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_624, fv_syn_c0] using (nb078_compact_fv_empty_0475 g)

theorem nb078_wpp_notmem_1604 : (nb078_alpha_dummy_614) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_614, fv_syn_c0] using (nb078_compact_fv_empty_0476)

theorem nb078_wpp_notmem_1605 (g : Var) : (nb078_alpha_dummy_616 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_616, fv_syn_c0] using (nb078_compact_fv_empty_0477 g)

theorem nb078_wpp_notmem_1606 : (nb078_alpha_dummy_613) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_613, fv_syn_c0] using (nb078_compact_fv_empty_0478)

theorem nb078_wpp_notmem_1607 (g : Var) : (nb078_alpha_dummy_615 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_615, fv_syn_c0] using (nb078_compact_fv_empty_0479 g)

theorem nb078_wpp_notmem_1608 : (nb078_alpha_dummy_619) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_619, fv_syn_c0] using (nb078_compact_fv_empty_0480)

theorem nb078_wpp_notmem_1609 (g : Var) : (nb078_alpha_dummy_620 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_620, fv_syn_c0] using (nb078_compact_fv_empty_0481 g)

theorem nb078_wpp_notmem_1610 : (nb078_alpha_dummy_617) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_617, fv_syn_c0] using (nb078_compact_fv_empty_0482)

theorem nb078_wpp_notmem_1611 (g : Var) : (nb078_alpha_dummy_618 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_618, fv_syn_c0] using (nb078_compact_fv_empty_0483 g)

theorem nb078_wpp_notmem_1612 : (nb078_alpha_dummy_571) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_571, fv_syn_c0] using (nb078_compact_fv_empty_0484)

theorem nb078_wpp_notmem_1613 (g : Var) : (nb078_alpha_dummy_574 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_574, fv_syn_c0] using (nb078_compact_fv_empty_0485 g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
