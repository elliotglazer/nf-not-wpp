import NAR4C078C001Part125

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

theorem nb078_compact_envfresh_0340 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_791) (nb078_alpha_dummy_794 h) (nb078_wpp_notmem_1934) (nb078_wpp_notmem_1935 h) (TEnvFresh.consFresh (nb078_alpha_dummy_790) (nb078_alpha_dummy_793 h) (nb078_wpp_notmem_1936) (nb078_wpp_notmem_1937 h) (TEnvFresh.consFresh (nb078_alpha_dummy_789) (nb078_alpha_dummy_792 h) (nb078_wpp_notmem_1938) (nb078_wpp_notmem_1939 h) (TEnvFresh.consFresh (nb078_alpha_dummy_787) (nb078_alpha_dummy_788 h) (nb078_wpp_notmem_1940) (nb078_wpp_notmem_1941 h) (TEnvFresh.consFresh (nb078_alpha_dummy_783) (nb078_alpha_dummy_785 h) (nb078_wpp_notmem_1942) (nb078_wpp_notmem_1943 h) (TEnvFresh.consFresh (nb078_alpha_dummy_784) (nb078_alpha_dummy_786 h) (nb078_wpp_notmem_1944) (nb078_wpp_notmem_1945 h) (TEnvFresh.consFresh (nb078_alpha_dummy_809) (nb078_alpha_dummy_810 h) (nb078_wpp_notmem_2024) (nb078_wpp_notmem_2025 h) (TEnvFresh.consFresh (nb078_alpha_dummy_807) (nb078_alpha_dummy_808 h) (nb078_wpp_notmem_2026) (nb078_wpp_notmem_2027 h) (TEnvFresh.consFresh (nb078_alpha_dummy_776) (nb078_alpha_dummy_778 h) (nb078_wpp_notmem_1946) (nb078_wpp_notmem_1947 h) (TEnvFresh.consFresh (nb078_alpha_dummy_775) (nb078_alpha_dummy_777 h) (nb078_wpp_notmem_1948) (nb078_wpp_notmem_1949 h) (TEnvFresh.consFresh (nb078_alpha_dummy_805) (nb078_alpha_dummy_806 h) (nb078_wpp_notmem_2028) (nb078_wpp_notmem_2029 h) (TEnvFresh.consFresh (nb078_alpha_dummy_779) (nb078_alpha_dummy_780 h) (nb078_wpp_notmem_1952) (nb078_wpp_notmem_1953 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1954) (nb078_wpp_notmem_1955 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1956) (nb078_wpp_notmem_1957 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1958) (nb078_wpp_notmem_1959 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1960) (nb078_wpp_notmem_1961 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1962) (nb078_wpp_notmem_1963 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb078_wpp_refl_0340 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0340 x y h)

theorem nb078_wpp_notmem_2030 : (nb078_alpha_dummy_809) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_809, fv_syn_c0] using (nb078_compact_fv_empty_0608)

theorem nb078_wpp_notmem_2031 (h : Var) : (nb078_alpha_dummy_810 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_810, fv_syn_c0] using (nb078_compact_fv_empty_0609 h)

theorem nb078_wpp_notmem_2032 : (nb078_alpha_dummy_807) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_807, fv_syn_c0] using (nb078_compact_fv_empty_0610)

theorem nb078_wpp_notmem_2033 (h : Var) : (nb078_alpha_dummy_808 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_808, fv_syn_c0] using (nb078_compact_fv_empty_0611 h)

theorem nb078_wpp_notmem_2034 : (nb078_alpha_dummy_805) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_805, fv_syn_c0] using (nb078_compact_fv_empty_0612)

theorem nb078_wpp_notmem_2035 (h : Var) : (nb078_alpha_dummy_806 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_806, fv_syn_c0] using (nb078_compact_fv_empty_0613 h)

theorem nb078_compact_envfresh_0341 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_791) (nb078_alpha_dummy_794 h) (nb078_wpp_notmem_1966) (nb078_wpp_notmem_1967 h) (TEnvFresh.consFresh (nb078_alpha_dummy_790) (nb078_alpha_dummy_793 h) (nb078_wpp_notmem_1968) (nb078_wpp_notmem_1969 h) (TEnvFresh.consFresh (nb078_alpha_dummy_789) (nb078_alpha_dummy_792 h) (nb078_wpp_notmem_1970) (nb078_wpp_notmem_1971 h) (TEnvFresh.consFresh (nb078_alpha_dummy_787) (nb078_alpha_dummy_788 h) (nb078_wpp_notmem_1972) (nb078_wpp_notmem_1973 h) (TEnvFresh.consFresh (nb078_alpha_dummy_783) (nb078_alpha_dummy_785 h) (nb078_wpp_notmem_1974) (nb078_wpp_notmem_1975 h) (TEnvFresh.consFresh (nb078_alpha_dummy_784) (nb078_alpha_dummy_786 h) (nb078_wpp_notmem_1976) (nb078_wpp_notmem_1977 h) (TEnvFresh.consFresh (nb078_alpha_dummy_809) (nb078_alpha_dummy_810 h) (nb078_wpp_notmem_2030) (nb078_wpp_notmem_2031 h) (TEnvFresh.consFresh (nb078_alpha_dummy_807) (nb078_alpha_dummy_808 h) (nb078_wpp_notmem_2032) (nb078_wpp_notmem_2033 h) (TEnvFresh.consFresh (nb078_alpha_dummy_776) (nb078_alpha_dummy_778 h) (nb078_wpp_notmem_1978) (nb078_wpp_notmem_1979 h) (TEnvFresh.consFresh (nb078_alpha_dummy_775) (nb078_alpha_dummy_777 h) (nb078_wpp_notmem_1980) (nb078_wpp_notmem_1981 h) (TEnvFresh.consFresh (nb078_alpha_dummy_805) (nb078_alpha_dummy_806 h) (nb078_wpp_notmem_2034) (nb078_wpp_notmem_2035 h) (TEnvFresh.consFresh (nb078_alpha_dummy_779) (nb078_alpha_dummy_780 h) (nb078_wpp_notmem_1984) (nb078_wpp_notmem_1985 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1986) (nb078_wpp_notmem_1987 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1988) (nb078_wpp_notmem_1989 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1990) (nb078_wpp_notmem_1991 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1992) (nb078_wpp_notmem_1993 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1994) (nb078_wpp_notmem_1995 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb078_wpp_refl_0341 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0341 x y h)

theorem nb078_wpp_notmem_2036 : (nb078_alpha_dummy_809) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_809, fv_syn_cnnc] using (nb078_compact_fv_empty_0608)

theorem nb078_wpp_notmem_2037 (h : Var) : (nb078_alpha_dummy_810 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_810, fv_syn_cnnc] using (nb078_compact_fv_empty_0609 h)

theorem nb078_wpp_notmem_2038 : (nb078_alpha_dummy_807) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_807, fv_syn_cnnc] using (nb078_compact_fv_empty_0610)

theorem nb078_wpp_notmem_2039 (h : Var) : (nb078_alpha_dummy_808 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_808, fv_syn_cnnc] using (nb078_compact_fv_empty_0611 h)

theorem nb078_wpp_notmem_2040 : (nb078_alpha_dummy_805) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_805, fv_syn_cnnc] using (nb078_compact_fv_empty_0612)

theorem nb078_wpp_notmem_2041 (h : Var) : (nb078_alpha_dummy_806 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_806, fv_syn_cnnc] using (nb078_compact_fv_empty_0613 h)

theorem nb078_compact_envfresh_0342 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_787) (nb078_alpha_dummy_788 h) (nb078_wpp_notmem_1998) (nb078_wpp_notmem_1999 h) (TEnvFresh.consFresh (nb078_alpha_dummy_783) (nb078_alpha_dummy_785 h) (nb078_wpp_notmem_2000) (nb078_wpp_notmem_2001 h) (TEnvFresh.consFresh (nb078_alpha_dummy_784) (nb078_alpha_dummy_786 h) (nb078_wpp_notmem_2002) (nb078_wpp_notmem_2003 h) (TEnvFresh.consFresh (nb078_alpha_dummy_809) (nb078_alpha_dummy_810 h) (nb078_wpp_notmem_2036) (nb078_wpp_notmem_2037 h) (TEnvFresh.consFresh (nb078_alpha_dummy_807) (nb078_alpha_dummy_808 h) (nb078_wpp_notmem_2038) (nb078_wpp_notmem_2039 h) (TEnvFresh.consFresh (nb078_alpha_dummy_776) (nb078_alpha_dummy_778 h) (nb078_wpp_notmem_2004) (nb078_wpp_notmem_2005 h) (TEnvFresh.consFresh (nb078_alpha_dummy_775) (nb078_alpha_dummy_777 h) (nb078_wpp_notmem_2006) (nb078_wpp_notmem_2007 h) (TEnvFresh.consFresh (nb078_alpha_dummy_805) (nb078_alpha_dummy_806 h) (nb078_wpp_notmem_2040) (nb078_wpp_notmem_2041 h) (TEnvFresh.consFresh (nb078_alpha_dummy_779) (nb078_alpha_dummy_780 h) (nb078_wpp_notmem_2010) (nb078_wpp_notmem_2011 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_2012) (nb078_wpp_notmem_2013 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_2014) (nb078_wpp_notmem_2015 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_2016) (nb078_wpp_notmem_2017 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_2018) (nb078_wpp_notmem_2019 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_2020) (nb078_wpp_notmem_2021 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0342 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0342 x y h)

theorem nb078_wpp_notmem_2042 : (nb078_alpha_dummy_807) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_807, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0610)

theorem nb078_wpp_notmem_2043 (h : Var) : (nb078_alpha_dummy_808 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_808, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0611 h)

theorem nb078_wpp_notmem_2044 : (nb078_alpha_dummy_776) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_776, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0588)

theorem nb078_wpp_notmem_2045 (h : Var) : (nb078_alpha_dummy_778 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_778, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0589 h)

theorem nb078_wpp_notmem_2046 : (nb078_alpha_dummy_775) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_775, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0590)

theorem nb078_wpp_notmem_2047 (h : Var) : (nb078_alpha_dummy_777 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_777, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0591 h)

theorem nb078_wpp_notmem_2048 : (nb078_alpha_dummy_805) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_805, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0612)

theorem nb078_wpp_notmem_2049 (h : Var) : (nb078_alpha_dummy_806 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_806, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0613 h)

theorem nb078_wpp_notmem_2050 : (nb078_alpha_dummy_779) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_779, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0594)

theorem nb078_wpp_notmem_2051 (h : Var) : (nb078_alpha_dummy_780 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_780, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0595 h)

theorem nb078_wpp_notmem_2052 : (nb078_alpha_dummy_768) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_768, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0596)

theorem nb078_wpp_notmem_2053 (h : Var) : (nb078_alpha_dummy_771 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_771, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0597 h)

theorem nb078_wpp_notmem_2054 : (nb078_alpha_dummy_767) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_767, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0598)

theorem nb078_wpp_notmem_2055 (h : Var) : (nb078_alpha_dummy_770 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_770, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0599 h)

theorem nb078_wpp_notmem_2056 : (nb078_alpha_dummy_773) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_773, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0600)

theorem nb078_wpp_notmem_2057 (h : Var) : (nb078_alpha_dummy_774 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_774, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0601 h)

theorem nb078_wpp_notmem_2058 : (nb078_alpha_dummy_765) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_765, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0602)

theorem nb078_wpp_notmem_2059 (h : Var) : (nb078_alpha_dummy_766 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_766, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0603 h)

theorem nb078_wpp_notmem_2060 : (nb078_alpha_dummy_763) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_763, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0604)

theorem nb078_wpp_notmem_2061 (h : Var) : (nb078_alpha_dummy_764 h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_764, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0605 h)

theorem nb078_wpp_notmem_2062 : (nb078_alpha_dummy_002) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0606)

theorem nb078_wpp_notmem_2063 (h : Var) : h ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0607 h)

theorem nb078_compact_envfresh_0343 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_807) (nb078_alpha_dummy_808 h) (nb078_wpp_notmem_2042) (nb078_wpp_notmem_2043 h) (TEnvFresh.consFresh (nb078_alpha_dummy_776) (nb078_alpha_dummy_778 h) (nb078_wpp_notmem_2044) (nb078_wpp_notmem_2045 h) (TEnvFresh.consFresh (nb078_alpha_dummy_775) (nb078_alpha_dummy_777 h) (nb078_wpp_notmem_2046) (nb078_wpp_notmem_2047 h) (TEnvFresh.consFresh (nb078_alpha_dummy_805) (nb078_alpha_dummy_806 h) (nb078_wpp_notmem_2048) (nb078_wpp_notmem_2049 h) (TEnvFresh.consFresh (nb078_alpha_dummy_779) (nb078_alpha_dummy_780 h) (nb078_wpp_notmem_2050) (nb078_wpp_notmem_2051 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_2052) (nb078_wpp_notmem_2053 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_2054) (nb078_wpp_notmem_2055 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_2056) (nb078_wpp_notmem_2057 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_2058) (nb078_wpp_notmem_2059 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_2060) (nb078_wpp_notmem_2061 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2062) (nb078_wpp_notmem_2063 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))

noncomputable def nb078_wpp_refl_0343 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0343 x y h)

noncomputable def nb078_split_alpha_0103 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_807)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_776))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_807)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_808 h)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_808 h)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0808) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0809 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0808) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0809 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0838) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0839 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0836) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0837 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_776))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_778 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0812) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0813 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0812) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0813 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0340 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0816) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0817 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0814) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0815 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0820) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0821 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0818) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0819 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0816) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0817 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0814) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0815 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0820) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0821 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0818) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0819 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0341 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0824) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0825 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0822) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0823 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0824) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0825 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0822) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0823 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0828) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0829 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0826) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0827 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0828) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0829 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0826) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0827 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0342 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0342 x y h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0808) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0809 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0808) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0809 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0838) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0839 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0836) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0837 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_776))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_778 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0812) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0813 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0812) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0813 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0340 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0816) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0817 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0814) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0815 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0820) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0821 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0818) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0819 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0816) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0817 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0814) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0815 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0820) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0821 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0818) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0819 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0341 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0824) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0825 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0822) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0823 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0824) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0825 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0822) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0823 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0828) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0829 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0826) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0827 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0828) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0829 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0826) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0827 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0342 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0342 x y h)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (nb078_wpp_refl_0343 x y h)))))

theorem nb078_compact_fv_empty_0614 : (nb078_alpha_dummy_827) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2064 : (nb078_alpha_dummy_827) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_827, fv_syn_c1c] using (nb078_compact_fv_empty_0614)

theorem nb078_compact_fv_empty_0615 (h : Var) : (nb078_alpha_dummy_830 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2065 (h : Var) : (nb078_alpha_dummy_830 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_830, fv_syn_c1c] using (nb078_compact_fv_empty_0615 h)

theorem nb078_compact_fv_empty_0616 : (nb078_alpha_dummy_826) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2066 : (nb078_alpha_dummy_826) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_826, fv_syn_c1c] using (nb078_compact_fv_empty_0616)

theorem nb078_compact_fv_empty_0617 (h : Var) : (nb078_alpha_dummy_829 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2067 (h : Var) : (nb078_alpha_dummy_829 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_829, fv_syn_c1c] using (nb078_compact_fv_empty_0617 h)

theorem nb078_compact_fv_empty_0618 : (nb078_alpha_dummy_825) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2068 : (nb078_alpha_dummy_825) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_825, fv_syn_c1c] using (nb078_compact_fv_empty_0618)

theorem nb078_compact_fv_empty_0619 (h : Var) : (nb078_alpha_dummy_828 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2069 (h : Var) : (nb078_alpha_dummy_828 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_828, fv_syn_c1c] using (nb078_compact_fv_empty_0619 h)

theorem nb078_compact_fv_empty_0620 : (nb078_alpha_dummy_823) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2070 : (nb078_alpha_dummy_823) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_823, fv_syn_c1c] using (nb078_compact_fv_empty_0620)

theorem nb078_compact_fv_empty_0621 (h : Var) : (nb078_alpha_dummy_824 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2071 (h : Var) : (nb078_alpha_dummy_824 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_824, fv_syn_c1c] using (nb078_compact_fv_empty_0621 h)

theorem nb078_compact_fv_empty_0622 : (nb078_alpha_dummy_819) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2072 : (nb078_alpha_dummy_819) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_819, fv_syn_c1c] using (nb078_compact_fv_empty_0622)

theorem nb078_compact_fv_empty_0623 (h : Var) : (nb078_alpha_dummy_821 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2073 (h : Var) : (nb078_alpha_dummy_821 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_821, fv_syn_c1c] using (nb078_compact_fv_empty_0623 h)

theorem nb078_compact_fv_empty_0624 : (nb078_alpha_dummy_820) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2074 : (nb078_alpha_dummy_820) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_820, fv_syn_c1c] using (nb078_compact_fv_empty_0624)

theorem nb078_compact_fv_empty_0625 (h : Var) : (nb078_alpha_dummy_822 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2075 (h : Var) : (nb078_alpha_dummy_822 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_822, fv_syn_c1c] using (nb078_compact_fv_empty_0625 h)

theorem nb078_compact_fv_empty_0626 : (nb078_alpha_dummy_812) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2076 : (nb078_alpha_dummy_812) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_812, fv_syn_c1c] using (nb078_compact_fv_empty_0626)

theorem nb078_compact_fv_empty_0627 (h : Var) : (nb078_alpha_dummy_814 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2077 (h : Var) : (nb078_alpha_dummy_814 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_814, fv_syn_c1c] using (nb078_compact_fv_empty_0627 h)

theorem nb078_compact_fv_empty_0628 : (nb078_alpha_dummy_811) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2078 : (nb078_alpha_dummy_811) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_811, fv_syn_c1c] using (nb078_compact_fv_empty_0628)

theorem nb078_compact_fv_empty_0629 (h : Var) : (nb078_alpha_dummy_813 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2079 (h : Var) : (nb078_alpha_dummy_813 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_813, fv_syn_c1c] using (nb078_compact_fv_empty_0629 h)

theorem nb078_compact_fv_empty_0630 : (nb078_alpha_dummy_817) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2080 : (nb078_alpha_dummy_817) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_817, fv_syn_c1c] using (nb078_compact_fv_empty_0630)

theorem nb078_compact_fv_empty_0631 (h : Var) : (nb078_alpha_dummy_818 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2081 (h : Var) : (nb078_alpha_dummy_818 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_818, fv_syn_c1c] using (nb078_compact_fv_empty_0631 h)

theorem nb078_compact_fv_empty_0632 : (nb078_alpha_dummy_815) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2082 : (nb078_alpha_dummy_815) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_815, fv_syn_c1c] using (nb078_compact_fv_empty_0632)

theorem nb078_compact_fv_empty_0633 (h : Var) : (nb078_alpha_dummy_816 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2083 (h : Var) : (nb078_alpha_dummy_816 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_816, fv_syn_c1c] using (nb078_compact_fv_empty_0633 h)

theorem nb078_compact_fv_empty_0634 : (nb078_alpha_dummy_769) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2084 : (nb078_alpha_dummy_769) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_769, fv_syn_c1c] using (nb078_compact_fv_empty_0634)

theorem nb078_compact_fv_empty_0635 (h : Var) : (nb078_alpha_dummy_772 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2085 (h : Var) : (nb078_alpha_dummy_772 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_772, fv_syn_c1c] using (nb078_compact_fv_empty_0635 h)

theorem nb078_compact_envfresh_0344 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826), (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)), ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)), ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)), ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_827) (nb078_alpha_dummy_830 h) (nb078_wpp_notmem_2064) (nb078_wpp_notmem_2065 h) (TEnvFresh.consFresh (nb078_alpha_dummy_826) (nb078_alpha_dummy_829 h) (nb078_wpp_notmem_2066) (nb078_wpp_notmem_2067 h) (TEnvFresh.consFresh (nb078_alpha_dummy_825) (nb078_alpha_dummy_828 h) (nb078_wpp_notmem_2068) (nb078_wpp_notmem_2069 h) (TEnvFresh.consFresh (nb078_alpha_dummy_823) (nb078_alpha_dummy_824 h) (nb078_wpp_notmem_2070) (nb078_wpp_notmem_2071 h) (TEnvFresh.consFresh (nb078_alpha_dummy_819) (nb078_alpha_dummy_821 h) (nb078_wpp_notmem_2072) (nb078_wpp_notmem_2073 h) (TEnvFresh.consFresh (nb078_alpha_dummy_820) (nb078_alpha_dummy_822 h) (nb078_wpp_notmem_2074) (nb078_wpp_notmem_2075 h) (TEnvFresh.consFresh (nb078_alpha_dummy_812) (nb078_alpha_dummy_814 h) (nb078_wpp_notmem_2076) (nb078_wpp_notmem_2077 h) (TEnvFresh.consFresh (nb078_alpha_dummy_811) (nb078_alpha_dummy_813 h) (nb078_wpp_notmem_2078) (nb078_wpp_notmem_2079 h) (TEnvFresh.consFresh (nb078_alpha_dummy_817) (nb078_alpha_dummy_818 h) (nb078_wpp_notmem_2080) (nb078_wpp_notmem_2081 h) (TEnvFresh.consFresh (nb078_alpha_dummy_815) (nb078_alpha_dummy_816 h) (nb078_wpp_notmem_2082) (nb078_wpp_notmem_2083 h) (TEnvFresh.consFresh (nb078_alpha_dummy_769) (nb078_alpha_dummy_772 h) (nb078_wpp_notmem_2084) (nb078_wpp_notmem_2085 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1954) (nb078_wpp_notmem_1955 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1956) (nb078_wpp_notmem_1957 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1958) (nb078_wpp_notmem_1959 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1960) (nb078_wpp_notmem_1961 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1962) (nb078_wpp_notmem_1963 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
