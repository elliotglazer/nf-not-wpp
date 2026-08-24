import NAR4C090C001Part111

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

theorem nb090_compact_envfresh_0305 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_747 A), (nb090_alpha_dummy_748 v u h)), ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_745 A), (nb090_alpha_dummy_746 v u h)), ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_747 A) (nb090_alpha_dummy_748 v u h) (nb090_wpp_notmem_1944 A) (nb090_wpp_notmem_1945 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_716 A) (nb090_alpha_dummy_718 v u h) (nb090_wpp_notmem_1946 A) (nb090_wpp_notmem_1947 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_715 A) (nb090_alpha_dummy_717 v u h) (nb090_wpp_notmem_1948 A) (nb090_wpp_notmem_1949 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_745 A) (nb090_alpha_dummy_746 v u h) (nb090_wpp_notmem_1950 A) (nb090_wpp_notmem_1951 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_719 A) (nb090_alpha_dummy_720 v u h) (nb090_wpp_notmem_1952 A) (nb090_wpp_notmem_1953 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_707 A) (nb090_alpha_dummy_708 v u h) (nb090_wpp_notmem_1954 A) (nb090_wpp_notmem_1955 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_709 A) (nb090_alpha_dummy_710 v u h) (nb090_wpp_notmem_1956 A) (nb090_wpp_notmem_1957 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_712 A) (nb090_alpha_dummy_714 v u h) (nb090_wpp_notmem_1958 A) (nb090_wpp_notmem_1959 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_711 A) (nb090_alpha_dummy_713 v u h) (nb090_wpp_notmem_1960 A) (nb090_wpp_notmem_1961 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_700 A) (nb090_alpha_dummy_702 v u h) (nb090_wpp_notmem_1962 A) (nb090_wpp_notmem_1963 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_699 A) (nb090_alpha_dummy_701 v u h) (nb090_wpp_notmem_1964 A) (nb090_wpp_notmem_1965 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_705 A) (nb090_alpha_dummy_706 v u h) (nb090_wpp_notmem_1966 A) (nb090_wpp_notmem_1967 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_703 A) (nb090_alpha_dummy_704 v u h) (nb090_wpp_notmem_1968 A) (nb090_wpp_notmem_1969 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1604 A) (nb090_wpp_notmem_1605 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1594 A) (nb090_wpp_notmem_1595 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))))))

noncomputable def nb090_wpp_refl_0305 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_747 A), (nb090_alpha_dummy_748 v u h)), ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_745 A), (nb090_alpha_dummy_746 v u h)), ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0305 v u A h)

theorem nb090_compact_fv_empty_0568 (A : Class) : (nb090_alpha_dummy_761 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1970 (A : Class) : (nb090_alpha_dummy_761 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_761, fv_syn_c1c] using (nb090_compact_fv_empty_0568 A)

theorem nb090_compact_fv_empty_0569 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_764 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1971 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_764 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_764, fv_syn_c1c] using (nb090_compact_fv_empty_0569 v u h)

theorem nb090_compact_fv_empty_0570 (A : Class) : (nb090_alpha_dummy_760 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1972 (A : Class) : (nb090_alpha_dummy_760 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_760, fv_syn_c1c] using (nb090_compact_fv_empty_0570 A)

theorem nb090_compact_fv_empty_0571 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_763 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1973 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_763 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_763, fv_syn_c1c] using (nb090_compact_fv_empty_0571 v u h)

theorem nb090_compact_fv_empty_0572 (A : Class) : (nb090_alpha_dummy_759 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1974 (A : Class) : (nb090_alpha_dummy_759 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_759, fv_syn_c1c] using (nb090_compact_fv_empty_0572 A)

theorem nb090_compact_fv_empty_0573 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_762 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1975 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_762 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_762, fv_syn_c1c] using (nb090_compact_fv_empty_0573 v u h)

theorem nb090_compact_fv_empty_0574 (A : Class) : (nb090_alpha_dummy_757 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1976 (A : Class) : (nb090_alpha_dummy_757 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_757, fv_syn_c1c] using (nb090_compact_fv_empty_0574 A)

theorem nb090_compact_fv_empty_0575 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_758 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1977 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_758 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_758, fv_syn_c1c] using (nb090_compact_fv_empty_0575 v u h)

theorem nb090_compact_fv_empty_0576 (A : Class) : (nb090_alpha_dummy_753 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1978 (A : Class) : (nb090_alpha_dummy_753 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_753, fv_syn_c1c] using (nb090_compact_fv_empty_0576 A)

theorem nb090_compact_fv_empty_0577 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_755 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1979 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_755 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_755, fv_syn_c1c] using (nb090_compact_fv_empty_0577 v u h)

theorem nb090_compact_fv_empty_0578 (A : Class) : (nb090_alpha_dummy_754 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1980 (A : Class) : (nb090_alpha_dummy_754 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_754, fv_syn_c1c] using (nb090_compact_fv_empty_0578 A)

theorem nb090_compact_fv_empty_0579 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_756 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1981 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_756 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_756, fv_syn_c1c] using (nb090_compact_fv_empty_0579 v u h)

theorem nb090_compact_envfresh_0306 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_761 A) (nb090_alpha_dummy_764 v u h) (nb090_wpp_notmem_1970 A) (nb090_wpp_notmem_1971 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_760 A) (nb090_alpha_dummy_763 v u h) (nb090_wpp_notmem_1972 A) (nb090_wpp_notmem_1973 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_759 A) (nb090_alpha_dummy_762 v u h) (nb090_wpp_notmem_1974 A) (nb090_wpp_notmem_1975 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_757 A) (nb090_alpha_dummy_758 v u h) (nb090_wpp_notmem_1976 A) (nb090_wpp_notmem_1977 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_753 A) (nb090_alpha_dummy_755 v u h) (nb090_wpp_notmem_1978 A) (nb090_wpp_notmem_1979 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_754 A) (nb090_alpha_dummy_756 v u h) (nb090_wpp_notmem_1980 A) (nb090_wpp_notmem_1981 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_700 A) (nb090_alpha_dummy_702 v u h) (nb090_wpp_notmem_1852 A) (nb090_wpp_notmem_1853 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_699 A) (nb090_alpha_dummy_701 v u h) (nb090_wpp_notmem_1854 A) (nb090_wpp_notmem_1855 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_705 A) (nb090_alpha_dummy_706 v u h) (nb090_wpp_notmem_1856 A) (nb090_wpp_notmem_1857 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_703 A) (nb090_alpha_dummy_704 v u h) (nb090_wpp_notmem_1858 A) (nb090_wpp_notmem_1859 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1598 A) (nb090_wpp_notmem_1599 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1588 A) (nb090_wpp_notmem_1589 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb090_wpp_refl_0306 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0306 v u A h)

theorem nb090_wpp_notmem_1982 (A : Class) : (nb090_alpha_dummy_761 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_761, fv_syn_c0] using (nb090_compact_fv_empty_0568 A)

theorem nb090_wpp_notmem_1983 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_764 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_764, fv_syn_c0] using (nb090_compact_fv_empty_0569 v u h)

theorem nb090_wpp_notmem_1984 (A : Class) : (nb090_alpha_dummy_760 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_760, fv_syn_c0] using (nb090_compact_fv_empty_0570 A)

theorem nb090_wpp_notmem_1985 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_763 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_763, fv_syn_c0] using (nb090_compact_fv_empty_0571 v u h)

theorem nb090_wpp_notmem_1986 (A : Class) : (nb090_alpha_dummy_759 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_759, fv_syn_c0] using (nb090_compact_fv_empty_0572 A)

theorem nb090_wpp_notmem_1987 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_762 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_762, fv_syn_c0] using (nb090_compact_fv_empty_0573 v u h)

theorem nb090_wpp_notmem_1988 (A : Class) : (nb090_alpha_dummy_757 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_757, fv_syn_c0] using (nb090_compact_fv_empty_0574 A)

theorem nb090_wpp_notmem_1989 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_758 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_758, fv_syn_c0] using (nb090_compact_fv_empty_0575 v u h)

theorem nb090_wpp_notmem_1990 (A : Class) : (nb090_alpha_dummy_753 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_753, fv_syn_c0] using (nb090_compact_fv_empty_0576 A)

theorem nb090_wpp_notmem_1991 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_755 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_755, fv_syn_c0] using (nb090_compact_fv_empty_0577 v u h)

theorem nb090_wpp_notmem_1992 (A : Class) : (nb090_alpha_dummy_754 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_754, fv_syn_c0] using (nb090_compact_fv_empty_0578 A)

theorem nb090_wpp_notmem_1993 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_756 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_756, fv_syn_c0] using (nb090_compact_fv_empty_0579 v u h)

theorem nb090_compact_envfresh_0307 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_761 A) (nb090_alpha_dummy_764 v u h) (nb090_wpp_notmem_1982 A) (nb090_wpp_notmem_1983 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_760 A) (nb090_alpha_dummy_763 v u h) (nb090_wpp_notmem_1984 A) (nb090_wpp_notmem_1985 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_759 A) (nb090_alpha_dummy_762 v u h) (nb090_wpp_notmem_1986 A) (nb090_wpp_notmem_1987 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_757 A) (nb090_alpha_dummy_758 v u h) (nb090_wpp_notmem_1988 A) (nb090_wpp_notmem_1989 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_753 A) (nb090_alpha_dummy_755 v u h) (nb090_wpp_notmem_1990 A) (nb090_wpp_notmem_1991 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_754 A) (nb090_alpha_dummy_756 v u h) (nb090_wpp_notmem_1992 A) (nb090_wpp_notmem_1993 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_700 A) (nb090_alpha_dummy_702 v u h) (nb090_wpp_notmem_1888 A) (nb090_wpp_notmem_1889 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_699 A) (nb090_alpha_dummy_701 v u h) (nb090_wpp_notmem_1890 A) (nb090_wpp_notmem_1891 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_705 A) (nb090_alpha_dummy_706 v u h) (nb090_wpp_notmem_1892 A) (nb090_wpp_notmem_1893 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_703 A) (nb090_alpha_dummy_704 v u h) (nb090_wpp_notmem_1894 A) (nb090_wpp_notmem_1895 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1600 A) (nb090_wpp_notmem_1601 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1590 A) (nb090_wpp_notmem_1591 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb090_wpp_refl_0307 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0307 v u A h)

theorem nb090_wpp_notmem_1994 (A : Class) : (nb090_alpha_dummy_757 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_757, fv_syn_cnnc] using (nb090_compact_fv_empty_0574 A)

theorem nb090_wpp_notmem_1995 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_758 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_758, fv_syn_cnnc] using (nb090_compact_fv_empty_0575 v u h)

theorem nb090_wpp_notmem_1996 (A : Class) : (nb090_alpha_dummy_753 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_753, fv_syn_cnnc] using (nb090_compact_fv_empty_0576 A)

theorem nb090_wpp_notmem_1997 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_755 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_755, fv_syn_cnnc] using (nb090_compact_fv_empty_0577 v u h)

theorem nb090_wpp_notmem_1998 (A : Class) : (nb090_alpha_dummy_754 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_754, fv_syn_cnnc] using (nb090_compact_fv_empty_0578 A)

theorem nb090_wpp_notmem_1999 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_756 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_756, fv_syn_cnnc] using (nb090_compact_fv_empty_0579 v u h)

theorem nb090_compact_envfresh_0308 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_757 A) (nb090_alpha_dummy_758 v u h) (nb090_wpp_notmem_1994 A) (nb090_wpp_notmem_1995 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_753 A) (nb090_alpha_dummy_755 v u h) (nb090_wpp_notmem_1996 A) (nb090_wpp_notmem_1997 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_754 A) (nb090_alpha_dummy_756 v u h) (nb090_wpp_notmem_1998 A) (nb090_wpp_notmem_1999 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_700 A) (nb090_alpha_dummy_702 v u h) (nb090_wpp_notmem_1918 A) (nb090_wpp_notmem_1919 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_699 A) (nb090_alpha_dummy_701 v u h) (nb090_wpp_notmem_1920 A) (nb090_wpp_notmem_1921 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_705 A) (nb090_alpha_dummy_706 v u h) (nb090_wpp_notmem_1922 A) (nb090_wpp_notmem_1923 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_703 A) (nb090_alpha_dummy_704 v u h) (nb090_wpp_notmem_1924 A) (nb090_wpp_notmem_1925 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1602 A) (nb090_wpp_notmem_1603 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1592 A) (nb090_wpp_notmem_1593 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb090_wpp_refl_0308 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0308 v u A h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
