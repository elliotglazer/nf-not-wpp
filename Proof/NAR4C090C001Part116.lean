import NAR4C090C001Part115

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

noncomputable def nb090_wpp_refl_0315 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A), (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u h)), ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789 A), (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778 v u h)), ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)), ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A), (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0315 v u A h)

theorem nb090_compact_fv_empty_0616 (A : Class) : (nb090_alpha_dummy_825 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2122 (A : Class) : (nb090_alpha_dummy_825 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_825, fv_syn_c1c] using (nb090_compact_fv_empty_0616 A)

theorem nb090_compact_fv_empty_0617 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_826 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2123 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_826 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_826, fv_syn_c1c] using (nb090_compact_fv_empty_0617 v u h)

theorem nb090_compact_fv_empty_0618 (A : Class) : (nb090_alpha_dummy_823 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2124 (A : Class) : (nb090_alpha_dummy_823 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_823, fv_syn_c1c] using (nb090_compact_fv_empty_0618 A)

theorem nb090_compact_fv_empty_0619 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_824 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2125 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_824 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_824, fv_syn_c1c] using (nb090_compact_fv_empty_0619 v u h)

theorem nb090_compact_envfresh_0316 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_761 A) (nb090_alpha_dummy_764 v u h) (nb090_wpp_notmem_1970 A) (nb090_wpp_notmem_1971 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_760 A) (nb090_alpha_dummy_763 v u h) (nb090_wpp_notmem_1972 A) (nb090_wpp_notmem_1973 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_759 A) (nb090_alpha_dummy_762 v u h) (nb090_wpp_notmem_1974 A) (nb090_wpp_notmem_1975 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_757 A) (nb090_alpha_dummy_758 v u h) (nb090_wpp_notmem_1976 A) (nb090_wpp_notmem_1977 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_753 A) (nb090_alpha_dummy_755 v u h) (nb090_wpp_notmem_1978 A) (nb090_wpp_notmem_1979 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_754 A) (nb090_alpha_dummy_756 v u h) (nb090_wpp_notmem_1980 A) (nb090_wpp_notmem_1981 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_825 A) (nb090_alpha_dummy_826 v u h) (nb090_wpp_notmem_2122 A) (nb090_wpp_notmem_2123 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_823 A) (nb090_alpha_dummy_824 v u h) (nb090_wpp_notmem_2124 A) (nb090_wpp_notmem_2125 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_700 A) (nb090_alpha_dummy_702 v u h) (nb090_wpp_notmem_1852 A) (nb090_wpp_notmem_1853 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_699 A) (nb090_alpha_dummy_701 v u h) (nb090_wpp_notmem_1854 A) (nb090_wpp_notmem_1855 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_775 A) (nb090_alpha_dummy_776 v u h) (nb090_wpp_notmem_2028 A) (nb090_wpp_notmem_2029 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_703 A) (nb090_alpha_dummy_704 v u h) (nb090_wpp_notmem_1858 A) (nb090_wpp_notmem_1859 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1598 A) (nb090_wpp_notmem_1599 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1588 A) (nb090_wpp_notmem_1589 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0316 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0316 v u A h)

theorem nb090_wpp_notmem_2126 (A : Class) : (nb090_alpha_dummy_825 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_825, fv_syn_c0] using (nb090_compact_fv_empty_0616 A)

theorem nb090_wpp_notmem_2127 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_826 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_826, fv_syn_c0] using (nb090_compact_fv_empty_0617 v u h)

theorem nb090_wpp_notmem_2128 (A : Class) : (nb090_alpha_dummy_823 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_823, fv_syn_c0] using (nb090_compact_fv_empty_0618 A)

theorem nb090_wpp_notmem_2129 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_824 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_824, fv_syn_c0] using (nb090_compact_fv_empty_0619 v u h)

theorem nb090_compact_envfresh_0317 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_761 A) (nb090_alpha_dummy_764 v u h) (nb090_wpp_notmem_1982 A) (nb090_wpp_notmem_1983 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_760 A) (nb090_alpha_dummy_763 v u h) (nb090_wpp_notmem_1984 A) (nb090_wpp_notmem_1985 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_759 A) (nb090_alpha_dummy_762 v u h) (nb090_wpp_notmem_1986 A) (nb090_wpp_notmem_1987 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_757 A) (nb090_alpha_dummy_758 v u h) (nb090_wpp_notmem_1988 A) (nb090_wpp_notmem_1989 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_753 A) (nb090_alpha_dummy_755 v u h) (nb090_wpp_notmem_1990 A) (nb090_wpp_notmem_1991 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_754 A) (nb090_alpha_dummy_756 v u h) (nb090_wpp_notmem_1992 A) (nb090_wpp_notmem_1993 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_825 A) (nb090_alpha_dummy_826 v u h) (nb090_wpp_notmem_2126 A) (nb090_wpp_notmem_2127 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_823 A) (nb090_alpha_dummy_824 v u h) (nb090_wpp_notmem_2128 A) (nb090_wpp_notmem_2129 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_700 A) (nb090_alpha_dummy_702 v u h) (nb090_wpp_notmem_1888 A) (nb090_wpp_notmem_1889 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_699 A) (nb090_alpha_dummy_701 v u h) (nb090_wpp_notmem_1890 A) (nb090_wpp_notmem_1891 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_775 A) (nb090_alpha_dummy_776 v u h) (nb090_wpp_notmem_2058 A) (nb090_wpp_notmem_2059 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_703 A) (nb090_alpha_dummy_704 v u h) (nb090_wpp_notmem_1894 A) (nb090_wpp_notmem_1895 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1600 A) (nb090_wpp_notmem_1601 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1590 A) (nb090_wpp_notmem_1591 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0317 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0317 v u A h)

theorem nb090_wpp_notmem_2130 (A : Class) : (nb090_alpha_dummy_825 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_825, fv_syn_cnnc] using (nb090_compact_fv_empty_0616 A)

theorem nb090_wpp_notmem_2131 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_826 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_826, fv_syn_cnnc] using (nb090_compact_fv_empty_0617 v u h)

theorem nb090_wpp_notmem_2132 (A : Class) : (nb090_alpha_dummy_823 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_823, fv_syn_cnnc] using (nb090_compact_fv_empty_0618 A)

theorem nb090_wpp_notmem_2133 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_824 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_824, fv_syn_cnnc] using (nb090_compact_fv_empty_0619 v u h)

theorem nb090_compact_envfresh_0318 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_757 A) (nb090_alpha_dummy_758 v u h) (nb090_wpp_notmem_1994 A) (nb090_wpp_notmem_1995 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_753 A) (nb090_alpha_dummy_755 v u h) (nb090_wpp_notmem_1996 A) (nb090_wpp_notmem_1997 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_754 A) (nb090_alpha_dummy_756 v u h) (nb090_wpp_notmem_1998 A) (nb090_wpp_notmem_1999 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_825 A) (nb090_alpha_dummy_826 v u h) (nb090_wpp_notmem_2130 A) (nb090_wpp_notmem_2131 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_823 A) (nb090_alpha_dummy_824 v u h) (nb090_wpp_notmem_2132 A) (nb090_wpp_notmem_2133 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_700 A) (nb090_alpha_dummy_702 v u h) (nb090_wpp_notmem_1918 A) (nb090_wpp_notmem_1919 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_699 A) (nb090_alpha_dummy_701 v u h) (nb090_wpp_notmem_1920 A) (nb090_wpp_notmem_1921 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_775 A) (nb090_alpha_dummy_776 v u h) (nb090_wpp_notmem_2082 A) (nb090_wpp_notmem_2083 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_703 A) (nb090_alpha_dummy_704 v u h) (nb090_wpp_notmem_1924 A) (nb090_wpp_notmem_1925 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1602 A) (nb090_wpp_notmem_1603 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1592 A) (nb090_wpp_notmem_1593 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb090_wpp_refl_0318 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0318 v u A h)

theorem nb090_wpp_notmem_2134 (A : Class) : (nb090_alpha_dummy_823 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_823, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0618 A)

theorem nb090_wpp_notmem_2135 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_824 v u h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_824, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0619 v u h)

theorem nb090_compact_envfresh_0319 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_823 A) (nb090_alpha_dummy_824 v u h) (nb090_wpp_notmem_2134 A) (nb090_wpp_notmem_2135 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_700 A) (nb090_alpha_dummy_702 v u h) (nb090_wpp_notmem_1962 A) (nb090_wpp_notmem_1963 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_699 A) (nb090_alpha_dummy_701 v u h) (nb090_wpp_notmem_1964 A) (nb090_wpp_notmem_1965 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_775 A) (nb090_alpha_dummy_776 v u h) (nb090_wpp_notmem_2120 A) (nb090_wpp_notmem_2121 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_703 A) (nb090_alpha_dummy_704 v u h) (nb090_wpp_notmem_1968 A) (nb090_wpp_notmem_1969 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1604 A) (nb090_wpp_notmem_1605 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1594 A) (nb090_wpp_notmem_1595 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))

noncomputable def nb090_wpp_refl_0319 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0319 v u A h)

noncomputable def nb090_split_alpha_0093 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c)))) (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) (by decide)) (freshVar_injective (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0794 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0795 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0794 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0795 v u h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0878 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0879 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0876 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0877 v u h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_700 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0798 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0799 v u h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0798 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0799 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0796 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0797 v u h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0316 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0802 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0803 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0800 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0801 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0806 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0807 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0804 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0805 v u h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0802 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0803 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0800 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0801 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0806 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0807 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0804 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0805 v u h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0317 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0810 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0811 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0808 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0809 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0810 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0811 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0808 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0809 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0814 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0815 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0812 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0813 v u h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0814 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0815 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0812 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0813 v u h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0796 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0797 v u h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0318 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0796 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0797 v u h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0796 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0797 v u h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0318 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0794 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0795 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0794 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0795 v u h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0878 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0879 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0876 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0877 v u h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_700 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0798 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0799 v u h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0798 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0799 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0796 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0797 v u h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0316 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0802 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0803 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0800 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0801 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0806 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0807 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0804 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0805 v u h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0802 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0803 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0800 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0801 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0806 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0807 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0804 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0805 v u h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A), (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A), (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0317 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0810 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0811 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0808 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0809 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0810 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0811 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0808 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0809 v u h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0814 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0815 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0812 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0813 v u h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0814 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0815 v u h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0812 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0813 v u h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0796 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0797 v u h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0318 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0796 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0797 v u h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0796 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0797 v u h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_757 A), (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A), (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A), (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A), (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0318 v u A h)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0319 v u A h)))))))))

theorem nb090_compact_fv_empty_0620 (A : Class) : (nb090_alpha_dummy_851 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2136 (A : Class) : (nb090_alpha_dummy_851 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_851, fv_syn_c1c] using (nb090_compact_fv_empty_0620 A)

theorem nb090_compact_fv_empty_0621 (v : Var) : (nb090_alpha_dummy_854 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2137 (v : Var) : (nb090_alpha_dummy_854 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_854, fv_syn_c1c] using (nb090_compact_fv_empty_0621 v)

theorem nb090_compact_fv_empty_0622 (A : Class) : (nb090_alpha_dummy_850 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2138 (A : Class) : (nb090_alpha_dummy_850 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_850, fv_syn_c1c] using (nb090_compact_fv_empty_0622 A)

theorem nb090_compact_fv_empty_0623 (v : Var) : (nb090_alpha_dummy_853 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2139 (v : Var) : (nb090_alpha_dummy_853 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_853, fv_syn_c1c] using (nb090_compact_fv_empty_0623 v)

theorem nb090_compact_fv_empty_0624 (A : Class) : (nb090_alpha_dummy_849 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2140 (A : Class) : (nb090_alpha_dummy_849 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_849, fv_syn_c1c] using (nb090_compact_fv_empty_0624 A)

theorem nb090_compact_fv_empty_0625 (v : Var) : (nb090_alpha_dummy_852 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2141 (v : Var) : (nb090_alpha_dummy_852 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_852, fv_syn_c1c] using (nb090_compact_fv_empty_0625 v)

theorem nb090_compact_fv_empty_0626 (A : Class) : (nb090_alpha_dummy_847 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2142 (A : Class) : (nb090_alpha_dummy_847 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_847, fv_syn_c1c] using (nb090_compact_fv_empty_0626 A)

theorem nb090_compact_fv_empty_0627 (v : Var) : (nb090_alpha_dummy_848 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2143 (v : Var) : (nb090_alpha_dummy_848 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_848, fv_syn_c1c] using (nb090_compact_fv_empty_0627 v)

theorem nb090_compact_fv_empty_0628 (A : Class) : (nb090_alpha_dummy_843 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2144 (A : Class) : (nb090_alpha_dummy_843 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_843, fv_syn_c1c] using (nb090_compact_fv_empty_0628 A)

theorem nb090_compact_fv_empty_0629 (v : Var) : (nb090_alpha_dummy_845 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2145 (v : Var) : (nb090_alpha_dummy_845 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_845, fv_syn_c1c] using (nb090_compact_fv_empty_0629 v)

theorem nb090_compact_fv_empty_0630 (A : Class) : (nb090_alpha_dummy_844 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2146 (A : Class) : (nb090_alpha_dummy_844 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_844, fv_syn_c1c] using (nb090_compact_fv_empty_0630 A)

theorem nb090_compact_fv_empty_0631 (v : Var) : (nb090_alpha_dummy_846 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2147 (v : Var) : (nb090_alpha_dummy_846 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_846, fv_syn_c1c] using (nb090_compact_fv_empty_0631 v)

theorem nb090_compact_fv_empty_0632 (A : Class) : (nb090_alpha_dummy_836 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2148 (A : Class) : (nb090_alpha_dummy_836 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_836, fv_syn_c1c] using (nb090_compact_fv_empty_0632 A)

theorem nb090_compact_fv_empty_0633 (v : Var) : (nb090_alpha_dummy_838 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2149 (v : Var) : (nb090_alpha_dummy_838 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_838, fv_syn_c1c] using (nb090_compact_fv_empty_0633 v)

theorem nb090_compact_fv_empty_0634 (A : Class) : (nb090_alpha_dummy_835 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2150 (A : Class) : (nb090_alpha_dummy_835 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_835, fv_syn_c1c] using (nb090_compact_fv_empty_0634 A)

theorem nb090_compact_fv_empty_0635 (v : Var) : (nb090_alpha_dummy_837 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2151 (v : Var) : (nb090_alpha_dummy_837 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_837, fv_syn_c1c] using (nb090_compact_fv_empty_0635 v)

theorem nb090_compact_fv_empty_0636 (A : Class) : (nb090_alpha_dummy_841 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2152 (A : Class) : (nb090_alpha_dummy_841 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_841, fv_syn_c1c] using (nb090_compact_fv_empty_0636 A)

theorem nb090_compact_fv_empty_0637 (v : Var) : (nb090_alpha_dummy_842 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2153 (v : Var) : (nb090_alpha_dummy_842 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_842, fv_syn_c1c] using (nb090_compact_fv_empty_0637 v)

theorem nb090_compact_fv_empty_0638 (A : Class) : (nb090_alpha_dummy_839 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2154 (A : Class) : (nb090_alpha_dummy_839 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_839, fv_syn_c1c] using (nb090_compact_fv_empty_0638 A)

theorem nb090_compact_fv_empty_0639 (v : Var) : (nb090_alpha_dummy_840 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2155 (v : Var) : (nb090_alpha_dummy_840 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_840, fv_syn_c1c] using (nb090_compact_fv_empty_0639 v)

theorem nb090_compact_fv_empty_0640 (A : Class) : (nb090_alpha_dummy_827 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2156 (A : Class) : (nb090_alpha_dummy_827 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_827, fv_syn_c1c] using (nb090_compact_fv_empty_0640 A)

theorem nb090_compact_fv_empty_0641 (v : Var) : (nb090_alpha_dummy_828 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2157 (v : Var) : (nb090_alpha_dummy_828 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_828, fv_syn_c1c] using (nb090_compact_fv_empty_0641 v)

theorem nb090_compact_fv_empty_0642 (A : Class) : (nb090_alpha_dummy_829 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2158 (A : Class) : (nb090_alpha_dummy_829 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_829, fv_syn_c1c] using (nb090_compact_fv_empty_0642 A)

theorem nb090_compact_fv_empty_0643 (v : Var) : (nb090_alpha_dummy_830 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2159 (v : Var) : (nb090_alpha_dummy_830 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_830, fv_syn_c1c] using (nb090_compact_fv_empty_0643 v)

theorem nb090_compact_fv_empty_0644 (A : Class) : (nb090_alpha_dummy_832 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2160 (A : Class) : (nb090_alpha_dummy_832 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_832, fv_syn_c1c] using (nb090_compact_fv_empty_0644 A)

theorem nb090_compact_fv_empty_0645 (v : Var) : (nb090_alpha_dummy_834 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2161 (v : Var) : (nb090_alpha_dummy_834 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_834, fv_syn_c1c] using (nb090_compact_fv_empty_0645 v)

theorem nb090_compact_fv_empty_0646 (A : Class) : (nb090_alpha_dummy_831 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2162 (A : Class) : (nb090_alpha_dummy_831 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_831, fv_syn_c1c] using (nb090_compact_fv_empty_0646 A)

theorem nb090_compact_fv_empty_0647 (v : Var) : (nb090_alpha_dummy_833 v) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_2163 (v : Var) : (nb090_alpha_dummy_833 v) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_833, fv_syn_c1c] using (nb090_compact_fv_empty_0647 v)

theorem nb090_compact_envfresh_0320 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_851 A), (nb090_alpha_dummy_854 v)), ((nb090_alpha_dummy_850 A), (nb090_alpha_dummy_853 v)), ((nb090_alpha_dummy_849 A), (nb090_alpha_dummy_852 v)), ((nb090_alpha_dummy_847 A), (nb090_alpha_dummy_848 v)), ((nb090_alpha_dummy_843 A), (nb090_alpha_dummy_845 v)), ((nb090_alpha_dummy_844 A), (nb090_alpha_dummy_846 v)), ((nb090_alpha_dummy_836 A), (nb090_alpha_dummy_838 v)), ((nb090_alpha_dummy_835 A), (nb090_alpha_dummy_837 v)), ((nb090_alpha_dummy_841 A), (nb090_alpha_dummy_842 v)), ((nb090_alpha_dummy_839 A), (nb090_alpha_dummy_840 v)), ((nb090_alpha_dummy_827 A), (nb090_alpha_dummy_828 v)), ((nb090_alpha_dummy_829 A), (nb090_alpha_dummy_830 v)), ((nb090_alpha_dummy_832 A), (nb090_alpha_dummy_834 v)), ((nb090_alpha_dummy_831 A), (nb090_alpha_dummy_833 v)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_851 A) (nb090_alpha_dummy_854 v) (nb090_wpp_notmem_2136 A) (nb090_wpp_notmem_2137 v) (TEnvFresh.consFresh (nb090_alpha_dummy_850 A) (nb090_alpha_dummy_853 v) (nb090_wpp_notmem_2138 A) (nb090_wpp_notmem_2139 v) (TEnvFresh.consFresh (nb090_alpha_dummy_849 A) (nb090_alpha_dummy_852 v) (nb090_wpp_notmem_2140 A) (nb090_wpp_notmem_2141 v) (TEnvFresh.consFresh (nb090_alpha_dummy_847 A) (nb090_alpha_dummy_848 v) (nb090_wpp_notmem_2142 A) (nb090_wpp_notmem_2143 v) (TEnvFresh.consFresh (nb090_alpha_dummy_843 A) (nb090_alpha_dummy_845 v) (nb090_wpp_notmem_2144 A) (nb090_wpp_notmem_2145 v) (TEnvFresh.consFresh (nb090_alpha_dummy_844 A) (nb090_alpha_dummy_846 v) (nb090_wpp_notmem_2146 A) (nb090_wpp_notmem_2147 v) (TEnvFresh.consFresh (nb090_alpha_dummy_836 A) (nb090_alpha_dummy_838 v) (nb090_wpp_notmem_2148 A) (nb090_wpp_notmem_2149 v) (TEnvFresh.consFresh (nb090_alpha_dummy_835 A) (nb090_alpha_dummy_837 v) (nb090_wpp_notmem_2150 A) (nb090_wpp_notmem_2151 v) (TEnvFresh.consFresh (nb090_alpha_dummy_841 A) (nb090_alpha_dummy_842 v) (nb090_wpp_notmem_2152 A) (nb090_wpp_notmem_2153 v) (TEnvFresh.consFresh (nb090_alpha_dummy_839 A) (nb090_alpha_dummy_840 v) (nb090_wpp_notmem_2154 A) (nb090_wpp_notmem_2155 v) (TEnvFresh.consFresh (nb090_alpha_dummy_827 A) (nb090_alpha_dummy_828 v) (nb090_wpp_notmem_2156 A) (nb090_wpp_notmem_2157 v) (TEnvFresh.consFresh (nb090_alpha_dummy_829 A) (nb090_alpha_dummy_830 v) (nb090_wpp_notmem_2158 A) (nb090_wpp_notmem_2159 v) (TEnvFresh.consFresh (nb090_alpha_dummy_832 A) (nb090_alpha_dummy_834 v) (nb090_wpp_notmem_2160 A) (nb090_wpp_notmem_2161 v) (TEnvFresh.consFresh (nb090_alpha_dummy_831 A) (nb090_alpha_dummy_833 v) (nb090_wpp_notmem_2162 A) (nb090_wpp_notmem_2163 v) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1598 A) (nb090_wpp_notmem_1599 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1588 A) (nb090_wpp_notmem_1589 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
