import NAR4C078C001Part124

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

theorem nb078_wpp_notmem_1936 : (nb078_alpha_dummy_790) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_790, fv_syn_c1c] using (nb078_compact_fv_empty_0578)

theorem nb078_compact_fv_empty_0579 (h : Var) : (nb078_alpha_dummy_793 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1937 (h : Var) : (nb078_alpha_dummy_793 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_793, fv_syn_c1c] using (nb078_compact_fv_empty_0579 h)

theorem nb078_compact_fv_empty_0580 : (nb078_alpha_dummy_789) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1938 : (nb078_alpha_dummy_789) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_789, fv_syn_c1c] using (nb078_compact_fv_empty_0580)

theorem nb078_compact_fv_empty_0581 (h : Var) : (nb078_alpha_dummy_792 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1939 (h : Var) : (nb078_alpha_dummy_792 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_792, fv_syn_c1c] using (nb078_compact_fv_empty_0581 h)

theorem nb078_compact_fv_empty_0582 : (nb078_alpha_dummy_787) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1940 : (nb078_alpha_dummy_787) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_787, fv_syn_c1c] using (nb078_compact_fv_empty_0582)

theorem nb078_compact_fv_empty_0583 (h : Var) : (nb078_alpha_dummy_788 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1941 (h : Var) : (nb078_alpha_dummy_788 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_788, fv_syn_c1c] using (nb078_compact_fv_empty_0583 h)

theorem nb078_compact_fv_empty_0584 : (nb078_alpha_dummy_783) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1942 : (nb078_alpha_dummy_783) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_783, fv_syn_c1c] using (nb078_compact_fv_empty_0584)

theorem nb078_compact_fv_empty_0585 (h : Var) : (nb078_alpha_dummy_785 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1943 (h : Var) : (nb078_alpha_dummy_785 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_785, fv_syn_c1c] using (nb078_compact_fv_empty_0585 h)

theorem nb078_compact_fv_empty_0586 : (nb078_alpha_dummy_784) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1944 : (nb078_alpha_dummy_784) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_784, fv_syn_c1c] using (nb078_compact_fv_empty_0586)

theorem nb078_compact_fv_empty_0587 (h : Var) : (nb078_alpha_dummy_786 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1945 (h : Var) : (nb078_alpha_dummy_786 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_786, fv_syn_c1c] using (nb078_compact_fv_empty_0587 h)

theorem nb078_compact_fv_empty_0588 : (nb078_alpha_dummy_776) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1946 : (nb078_alpha_dummy_776) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_776, fv_syn_c1c] using (nb078_compact_fv_empty_0588)

theorem nb078_compact_fv_empty_0589 (h : Var) : (nb078_alpha_dummy_778 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1947 (h : Var) : (nb078_alpha_dummy_778 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_778, fv_syn_c1c] using (nb078_compact_fv_empty_0589 h)

theorem nb078_compact_fv_empty_0590 : (nb078_alpha_dummy_775) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1948 : (nb078_alpha_dummy_775) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_775, fv_syn_c1c] using (nb078_compact_fv_empty_0590)

theorem nb078_compact_fv_empty_0591 (h : Var) : (nb078_alpha_dummy_777 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1949 (h : Var) : (nb078_alpha_dummy_777 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_777, fv_syn_c1c] using (nb078_compact_fv_empty_0591 h)

theorem nb078_compact_fv_empty_0592 : (nb078_alpha_dummy_781) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1950 : (nb078_alpha_dummy_781) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_781, fv_syn_c1c] using (nb078_compact_fv_empty_0592)

theorem nb078_compact_fv_empty_0593 (h : Var) : (nb078_alpha_dummy_782 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1951 (h : Var) : (nb078_alpha_dummy_782 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_782, fv_syn_c1c] using (nb078_compact_fv_empty_0593 h)

theorem nb078_compact_fv_empty_0594 : (nb078_alpha_dummy_779) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1952 : (nb078_alpha_dummy_779) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_779, fv_syn_c1c] using (nb078_compact_fv_empty_0594)

theorem nb078_compact_fv_empty_0595 (h : Var) : (nb078_alpha_dummy_780 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1953 (h : Var) : (nb078_alpha_dummy_780 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_780, fv_syn_c1c] using (nb078_compact_fv_empty_0595 h)

theorem nb078_compact_fv_empty_0596 : (nb078_alpha_dummy_768) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1954 : (nb078_alpha_dummy_768) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_768, fv_syn_c1c] using (nb078_compact_fv_empty_0596)

theorem nb078_compact_fv_empty_0597 (h : Var) : (nb078_alpha_dummy_771 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1955 (h : Var) : (nb078_alpha_dummy_771 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_771, fv_syn_c1c] using (nb078_compact_fv_empty_0597 h)

theorem nb078_compact_fv_empty_0598 : (nb078_alpha_dummy_767) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1956 : (nb078_alpha_dummy_767) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_767, fv_syn_c1c] using (nb078_compact_fv_empty_0598)

theorem nb078_compact_fv_empty_0599 (h : Var) : (nb078_alpha_dummy_770 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1957 (h : Var) : (nb078_alpha_dummy_770 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_770, fv_syn_c1c] using (nb078_compact_fv_empty_0599 h)

theorem nb078_compact_fv_empty_0600 : (nb078_alpha_dummy_773) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1958 : (nb078_alpha_dummy_773) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_773, fv_syn_c1c] using (nb078_compact_fv_empty_0600)

theorem nb078_compact_fv_empty_0601 (h : Var) : (nb078_alpha_dummy_774 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1959 (h : Var) : (nb078_alpha_dummy_774 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_774, fv_syn_c1c] using (nb078_compact_fv_empty_0601 h)

theorem nb078_compact_fv_empty_0602 : (nb078_alpha_dummy_765) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1960 : (nb078_alpha_dummy_765) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_765, fv_syn_c1c] using (nb078_compact_fv_empty_0602)

theorem nb078_compact_fv_empty_0603 (h : Var) : (nb078_alpha_dummy_766 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1961 (h : Var) : (nb078_alpha_dummy_766 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_766, fv_syn_c1c] using (nb078_compact_fv_empty_0603 h)

theorem nb078_compact_fv_empty_0604 : (nb078_alpha_dummy_763) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1962 : (nb078_alpha_dummy_763) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_763, fv_syn_c1c] using (nb078_compact_fv_empty_0604)

theorem nb078_compact_fv_empty_0605 (h : Var) : (nb078_alpha_dummy_764 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1963 (h : Var) : (nb078_alpha_dummy_764 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_764, fv_syn_c1c] using (nb078_compact_fv_empty_0605 h)

theorem nb078_compact_fv_empty_0606 : (nb078_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1964 : (nb078_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_002, fv_syn_c1c] using (nb078_compact_fv_empty_0606)

theorem nb078_compact_fv_empty_0607 (h : Var) : h ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1965 (h : Var) : h ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb078_compact_fv_empty_0607 h)

theorem nb078_compact_envfresh_0337 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_791) (nb078_alpha_dummy_794 h) (nb078_wpp_notmem_1934) (nb078_wpp_notmem_1935 h) (TEnvFresh.consFresh (nb078_alpha_dummy_790) (nb078_alpha_dummy_793 h) (nb078_wpp_notmem_1936) (nb078_wpp_notmem_1937 h) (TEnvFresh.consFresh (nb078_alpha_dummy_789) (nb078_alpha_dummy_792 h) (nb078_wpp_notmem_1938) (nb078_wpp_notmem_1939 h) (TEnvFresh.consFresh (nb078_alpha_dummy_787) (nb078_alpha_dummy_788 h) (nb078_wpp_notmem_1940) (nb078_wpp_notmem_1941 h) (TEnvFresh.consFresh (nb078_alpha_dummy_783) (nb078_alpha_dummy_785 h) (nb078_wpp_notmem_1942) (nb078_wpp_notmem_1943 h) (TEnvFresh.consFresh (nb078_alpha_dummy_784) (nb078_alpha_dummy_786 h) (nb078_wpp_notmem_1944) (nb078_wpp_notmem_1945 h) (TEnvFresh.consFresh (nb078_alpha_dummy_776) (nb078_alpha_dummy_778 h) (nb078_wpp_notmem_1946) (nb078_wpp_notmem_1947 h) (TEnvFresh.consFresh (nb078_alpha_dummy_775) (nb078_alpha_dummy_777 h) (nb078_wpp_notmem_1948) (nb078_wpp_notmem_1949 h) (TEnvFresh.consFresh (nb078_alpha_dummy_781) (nb078_alpha_dummy_782 h) (nb078_wpp_notmem_1950) (nb078_wpp_notmem_1951 h) (TEnvFresh.consFresh (nb078_alpha_dummy_779) (nb078_alpha_dummy_780 h) (nb078_wpp_notmem_1952) (nb078_wpp_notmem_1953 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1954) (nb078_wpp_notmem_1955 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1956) (nb078_wpp_notmem_1957 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1958) (nb078_wpp_notmem_1959 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1960) (nb078_wpp_notmem_1961 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1962) (nb078_wpp_notmem_1963 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1964) (nb078_wpp_notmem_1965 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb078_wpp_refl_0337 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0337 x y h)

theorem nb078_wpp_notmem_1966 : (nb078_alpha_dummy_791) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_791, fv_syn_c0] using (nb078_compact_fv_empty_0576)

theorem nb078_wpp_notmem_1967 (h : Var) : (nb078_alpha_dummy_794 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_794, fv_syn_c0] using (nb078_compact_fv_empty_0577 h)

theorem nb078_wpp_notmem_1968 : (nb078_alpha_dummy_790) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_790, fv_syn_c0] using (nb078_compact_fv_empty_0578)

theorem nb078_wpp_notmem_1969 (h : Var) : (nb078_alpha_dummy_793 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_793, fv_syn_c0] using (nb078_compact_fv_empty_0579 h)

theorem nb078_wpp_notmem_1970 : (nb078_alpha_dummy_789) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_789, fv_syn_c0] using (nb078_compact_fv_empty_0580)

theorem nb078_wpp_notmem_1971 (h : Var) : (nb078_alpha_dummy_792 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_792, fv_syn_c0] using (nb078_compact_fv_empty_0581 h)

theorem nb078_wpp_notmem_1972 : (nb078_alpha_dummy_787) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_787, fv_syn_c0] using (nb078_compact_fv_empty_0582)

theorem nb078_wpp_notmem_1973 (h : Var) : (nb078_alpha_dummy_788 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_788, fv_syn_c0] using (nb078_compact_fv_empty_0583 h)

theorem nb078_wpp_notmem_1974 : (nb078_alpha_dummy_783) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_783, fv_syn_c0] using (nb078_compact_fv_empty_0584)

theorem nb078_wpp_notmem_1975 (h : Var) : (nb078_alpha_dummy_785 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_785, fv_syn_c0] using (nb078_compact_fv_empty_0585 h)

theorem nb078_wpp_notmem_1976 : (nb078_alpha_dummy_784) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_784, fv_syn_c0] using (nb078_compact_fv_empty_0586)

theorem nb078_wpp_notmem_1977 (h : Var) : (nb078_alpha_dummy_786 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_786, fv_syn_c0] using (nb078_compact_fv_empty_0587 h)

theorem nb078_wpp_notmem_1978 : (nb078_alpha_dummy_776) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_776, fv_syn_c0] using (nb078_compact_fv_empty_0588)

theorem nb078_wpp_notmem_1979 (h : Var) : (nb078_alpha_dummy_778 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_778, fv_syn_c0] using (nb078_compact_fv_empty_0589 h)

theorem nb078_wpp_notmem_1980 : (nb078_alpha_dummy_775) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_775, fv_syn_c0] using (nb078_compact_fv_empty_0590)

theorem nb078_wpp_notmem_1981 (h : Var) : (nb078_alpha_dummy_777 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_777, fv_syn_c0] using (nb078_compact_fv_empty_0591 h)

theorem nb078_wpp_notmem_1982 : (nb078_alpha_dummy_781) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_781, fv_syn_c0] using (nb078_compact_fv_empty_0592)

theorem nb078_wpp_notmem_1983 (h : Var) : (nb078_alpha_dummy_782 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_782, fv_syn_c0] using (nb078_compact_fv_empty_0593 h)

theorem nb078_wpp_notmem_1984 : (nb078_alpha_dummy_779) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_779, fv_syn_c0] using (nb078_compact_fv_empty_0594)

theorem nb078_wpp_notmem_1985 (h : Var) : (nb078_alpha_dummy_780 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_780, fv_syn_c0] using (nb078_compact_fv_empty_0595 h)

theorem nb078_wpp_notmem_1986 : (nb078_alpha_dummy_768) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_768, fv_syn_c0] using (nb078_compact_fv_empty_0596)

theorem nb078_wpp_notmem_1987 (h : Var) : (nb078_alpha_dummy_771 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_771, fv_syn_c0] using (nb078_compact_fv_empty_0597 h)

theorem nb078_wpp_notmem_1988 : (nb078_alpha_dummy_767) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_767, fv_syn_c0] using (nb078_compact_fv_empty_0598)

theorem nb078_wpp_notmem_1989 (h : Var) : (nb078_alpha_dummy_770 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_770, fv_syn_c0] using (nb078_compact_fv_empty_0599 h)

theorem nb078_wpp_notmem_1990 : (nb078_alpha_dummy_773) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_773, fv_syn_c0] using (nb078_compact_fv_empty_0600)

theorem nb078_wpp_notmem_1991 (h : Var) : (nb078_alpha_dummy_774 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_774, fv_syn_c0] using (nb078_compact_fv_empty_0601 h)

theorem nb078_wpp_notmem_1992 : (nb078_alpha_dummy_765) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_765, fv_syn_c0] using (nb078_compact_fv_empty_0602)

theorem nb078_wpp_notmem_1993 (h : Var) : (nb078_alpha_dummy_766 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_766, fv_syn_c0] using (nb078_compact_fv_empty_0603 h)

theorem nb078_wpp_notmem_1994 : (nb078_alpha_dummy_763) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_763, fv_syn_c0] using (nb078_compact_fv_empty_0604)

theorem nb078_wpp_notmem_1995 (h : Var) : (nb078_alpha_dummy_764 h) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_764, fv_syn_c0] using (nb078_compact_fv_empty_0605 h)

theorem nb078_wpp_notmem_1996 : (nb078_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_002, fv_syn_c0] using (nb078_compact_fv_empty_0606)

theorem nb078_wpp_notmem_1997 (h : Var) : h ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb078_compact_fv_empty_0607 h)

theorem nb078_compact_envfresh_0338 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_791) (nb078_alpha_dummy_794 h) (nb078_wpp_notmem_1966) (nb078_wpp_notmem_1967 h) (TEnvFresh.consFresh (nb078_alpha_dummy_790) (nb078_alpha_dummy_793 h) (nb078_wpp_notmem_1968) (nb078_wpp_notmem_1969 h) (TEnvFresh.consFresh (nb078_alpha_dummy_789) (nb078_alpha_dummy_792 h) (nb078_wpp_notmem_1970) (nb078_wpp_notmem_1971 h) (TEnvFresh.consFresh (nb078_alpha_dummy_787) (nb078_alpha_dummy_788 h) (nb078_wpp_notmem_1972) (nb078_wpp_notmem_1973 h) (TEnvFresh.consFresh (nb078_alpha_dummy_783) (nb078_alpha_dummy_785 h) (nb078_wpp_notmem_1974) (nb078_wpp_notmem_1975 h) (TEnvFresh.consFresh (nb078_alpha_dummy_784) (nb078_alpha_dummy_786 h) (nb078_wpp_notmem_1976) (nb078_wpp_notmem_1977 h) (TEnvFresh.consFresh (nb078_alpha_dummy_776) (nb078_alpha_dummy_778 h) (nb078_wpp_notmem_1978) (nb078_wpp_notmem_1979 h) (TEnvFresh.consFresh (nb078_alpha_dummy_775) (nb078_alpha_dummy_777 h) (nb078_wpp_notmem_1980) (nb078_wpp_notmem_1981 h) (TEnvFresh.consFresh (nb078_alpha_dummy_781) (nb078_alpha_dummy_782 h) (nb078_wpp_notmem_1982) (nb078_wpp_notmem_1983 h) (TEnvFresh.consFresh (nb078_alpha_dummy_779) (nb078_alpha_dummy_780 h) (nb078_wpp_notmem_1984) (nb078_wpp_notmem_1985 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_1986) (nb078_wpp_notmem_1987 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_1988) (nb078_wpp_notmem_1989 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_1990) (nb078_wpp_notmem_1991 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_1992) (nb078_wpp_notmem_1993 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_1994) (nb078_wpp_notmem_1995 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_1996) (nb078_wpp_notmem_1997 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb078_wpp_refl_0338 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0338 x y h)

theorem nb078_wpp_notmem_1998 : (nb078_alpha_dummy_787) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_787, fv_syn_cnnc] using (nb078_compact_fv_empty_0582)

theorem nb078_wpp_notmem_1999 (h : Var) : (nb078_alpha_dummy_788 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_788, fv_syn_cnnc] using (nb078_compact_fv_empty_0583 h)

theorem nb078_wpp_notmem_2000 : (nb078_alpha_dummy_783) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_783, fv_syn_cnnc] using (nb078_compact_fv_empty_0584)

theorem nb078_wpp_notmem_2001 (h : Var) : (nb078_alpha_dummy_785 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_785, fv_syn_cnnc] using (nb078_compact_fv_empty_0585 h)

theorem nb078_wpp_notmem_2002 : (nb078_alpha_dummy_784) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_784, fv_syn_cnnc] using (nb078_compact_fv_empty_0586)

theorem nb078_wpp_notmem_2003 (h : Var) : (nb078_alpha_dummy_786 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_786, fv_syn_cnnc] using (nb078_compact_fv_empty_0587 h)

theorem nb078_wpp_notmem_2004 : (nb078_alpha_dummy_776) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_776, fv_syn_cnnc] using (nb078_compact_fv_empty_0588)

theorem nb078_wpp_notmem_2005 (h : Var) : (nb078_alpha_dummy_778 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_778, fv_syn_cnnc] using (nb078_compact_fv_empty_0589 h)

theorem nb078_wpp_notmem_2006 : (nb078_alpha_dummy_775) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_775, fv_syn_cnnc] using (nb078_compact_fv_empty_0590)

theorem nb078_wpp_notmem_2007 (h : Var) : (nb078_alpha_dummy_777 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_777, fv_syn_cnnc] using (nb078_compact_fv_empty_0591 h)

theorem nb078_wpp_notmem_2008 : (nb078_alpha_dummy_781) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_781, fv_syn_cnnc] using (nb078_compact_fv_empty_0592)

theorem nb078_wpp_notmem_2009 (h : Var) : (nb078_alpha_dummy_782 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_782, fv_syn_cnnc] using (nb078_compact_fv_empty_0593 h)

theorem nb078_wpp_notmem_2010 : (nb078_alpha_dummy_779) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_779, fv_syn_cnnc] using (nb078_compact_fv_empty_0594)

theorem nb078_wpp_notmem_2011 (h : Var) : (nb078_alpha_dummy_780 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_780, fv_syn_cnnc] using (nb078_compact_fv_empty_0595 h)

theorem nb078_wpp_notmem_2012 : (nb078_alpha_dummy_768) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_768, fv_syn_cnnc] using (nb078_compact_fv_empty_0596)

theorem nb078_wpp_notmem_2013 (h : Var) : (nb078_alpha_dummy_771 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_771, fv_syn_cnnc] using (nb078_compact_fv_empty_0597 h)

theorem nb078_wpp_notmem_2014 : (nb078_alpha_dummy_767) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_767, fv_syn_cnnc] using (nb078_compact_fv_empty_0598)

theorem nb078_wpp_notmem_2015 (h : Var) : (nb078_alpha_dummy_770 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_770, fv_syn_cnnc] using (nb078_compact_fv_empty_0599 h)

theorem nb078_wpp_notmem_2016 : (nb078_alpha_dummy_773) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_773, fv_syn_cnnc] using (nb078_compact_fv_empty_0600)

theorem nb078_wpp_notmem_2017 (h : Var) : (nb078_alpha_dummy_774 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_774, fv_syn_cnnc] using (nb078_compact_fv_empty_0601 h)

theorem nb078_wpp_notmem_2018 : (nb078_alpha_dummy_765) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_765, fv_syn_cnnc] using (nb078_compact_fv_empty_0602)

theorem nb078_wpp_notmem_2019 (h : Var) : (nb078_alpha_dummy_766 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_766, fv_syn_cnnc] using (nb078_compact_fv_empty_0603 h)

theorem nb078_wpp_notmem_2020 : (nb078_alpha_dummy_763) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_763, fv_syn_cnnc] using (nb078_compact_fv_empty_0604)

theorem nb078_wpp_notmem_2021 (h : Var) : (nb078_alpha_dummy_764 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_764, fv_syn_cnnc] using (nb078_compact_fv_empty_0605 h)

theorem nb078_wpp_notmem_2022 : (nb078_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_002, fv_syn_cnnc] using (nb078_compact_fv_empty_0606)

theorem nb078_wpp_notmem_2023 (h : Var) : h ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb078_compact_fv_empty_0607 h)

theorem nb078_compact_envfresh_0339 (x : Var) (y : Var) (h : Var) : TEnvFresh [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_787) (nb078_alpha_dummy_788 h) (nb078_wpp_notmem_1998) (nb078_wpp_notmem_1999 h) (TEnvFresh.consFresh (nb078_alpha_dummy_783) (nb078_alpha_dummy_785 h) (nb078_wpp_notmem_2000) (nb078_wpp_notmem_2001 h) (TEnvFresh.consFresh (nb078_alpha_dummy_784) (nb078_alpha_dummy_786 h) (nb078_wpp_notmem_2002) (nb078_wpp_notmem_2003 h) (TEnvFresh.consFresh (nb078_alpha_dummy_776) (nb078_alpha_dummy_778 h) (nb078_wpp_notmem_2004) (nb078_wpp_notmem_2005 h) (TEnvFresh.consFresh (nb078_alpha_dummy_775) (nb078_alpha_dummy_777 h) (nb078_wpp_notmem_2006) (nb078_wpp_notmem_2007 h) (TEnvFresh.consFresh (nb078_alpha_dummy_781) (nb078_alpha_dummy_782 h) (nb078_wpp_notmem_2008) (nb078_wpp_notmem_2009 h) (TEnvFresh.consFresh (nb078_alpha_dummy_779) (nb078_alpha_dummy_780 h) (nb078_wpp_notmem_2010) (nb078_wpp_notmem_2011 h) (TEnvFresh.consFresh (nb078_alpha_dummy_768) (nb078_alpha_dummy_771 h) (nb078_wpp_notmem_2012) (nb078_wpp_notmem_2013 h) (TEnvFresh.consFresh (nb078_alpha_dummy_767) (nb078_alpha_dummy_770 h) (nb078_wpp_notmem_2014) (nb078_wpp_notmem_2015 h) (TEnvFresh.consFresh (nb078_alpha_dummy_773) (nb078_alpha_dummy_774 h) (nb078_wpp_notmem_2016) (nb078_wpp_notmem_2017 h) (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h) (nb078_wpp_notmem_2018) (nb078_wpp_notmem_2019 h) (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h) (nb078_wpp_notmem_2020) (nb078_wpp_notmem_2021 h) (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2022) (nb078_wpp_notmem_2023 h) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0339 (x : Var) (y : Var) (h : Var) : TReflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0339 x y h)

noncomputable def nb078_split_alpha_0102 (x : Var) (y : Var) (h : Var) : TAlphaWff [((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_781)) (Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_781)) (Class.cab (nb078_alpha_dummy_775) (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_775)) (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_782 h)) (Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_782 h)) (Class.cab (nb078_alpha_dummy_777 h) (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0806) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0807 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0803) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0805 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0808) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0809 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0808) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0809 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_776))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_778 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0812) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0813 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0812) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0813 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0337 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0816) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0817 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0814) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0815 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0820) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0821 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0818) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0819 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0816) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0817 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0814) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0815 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0820) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0821 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0818) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0819 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0338 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0824) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0825 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0822) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0823 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0824) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0825 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0822) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0823 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0828) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0829 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0826) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0827 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0828) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0829 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0826) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0827 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0339 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0339 x y h)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0806) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0807 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0803) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0805 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0808) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0809 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0808) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0809 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_776))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_778 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0812) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0813 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0812) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0813 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0337 x y h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0816) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0817 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0814) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0815 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0820) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0821 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0818) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0819 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0816) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0817 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0814) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0815 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0820) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0821 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0818) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0819 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790), (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)), ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0338 x y h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0824) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0825 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0822) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0823 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0824) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0825 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0822) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0823 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0828) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0829 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0826) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0827 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0828) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0829 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0826) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0827 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0339 x y h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0810) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0811 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)), ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0339 x y h))))))))))))))))))))))))))))

theorem nb078_compact_fv_empty_0608 : (nb078_alpha_dummy_809) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2024 : (nb078_alpha_dummy_809) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_809, fv_syn_c1c] using (nb078_compact_fv_empty_0608)

theorem nb078_compact_fv_empty_0609 (h : Var) : (nb078_alpha_dummy_810 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2025 (h : Var) : (nb078_alpha_dummy_810 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_810, fv_syn_c1c] using (nb078_compact_fv_empty_0609 h)

theorem nb078_compact_fv_empty_0610 : (nb078_alpha_dummy_807) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2026 : (nb078_alpha_dummy_807) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_807, fv_syn_c1c] using (nb078_compact_fv_empty_0610)

theorem nb078_compact_fv_empty_0611 (h : Var) : (nb078_alpha_dummy_808 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2027 (h : Var) : (nb078_alpha_dummy_808 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_808, fv_syn_c1c] using (nb078_compact_fv_empty_0611 h)

theorem nb078_compact_fv_empty_0612 : (nb078_alpha_dummy_805) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2028 : (nb078_alpha_dummy_805) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_805, fv_syn_c1c] using (nb078_compact_fv_empty_0612)

theorem nb078_compact_fv_empty_0613 (h : Var) : (nb078_alpha_dummy_806 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_2029 (h : Var) : (nb078_alpha_dummy_806 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_806, fv_syn_c1c] using (nb078_compact_fv_empty_0613 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
