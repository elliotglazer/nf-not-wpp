import NAR4C090C001Part007

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

theorem nb090_distinct_092 (A : Class) : (nb090_alpha_dummy_711 A) ≠ (nb090_alpha_dummy_712 A) := by
  simpa only [nb090_alpha_dummy_711, nb090_alpha_dummy_712] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A) (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_093 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_713 v u h) ∉ (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_708 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) := by
  simpa only [nb090_alpha_dummy_713] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_708 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) 0

theorem nb090_fresh_094 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_714 v u h) ∉ (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_708 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) := by
  simpa only [nb090_alpha_dummy_714] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_708 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) 1

theorem nb090_distinct_095 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_713 v u h) ≠ (nb090_alpha_dummy_714 v u h) := by
  simpa only [nb090_alpha_dummy_713, nb090_alpha_dummy_714] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_708 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_096 (A : Class) : (nb090_alpha_dummy_721 A) ∉ (((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_721] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv) 0

theorem nb090_fresh_097 (A : Class) : (nb090_alpha_dummy_745 A) ∉ (((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_745] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A) (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_098 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_722 v u h) ∉ (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv) := by
  simpa only [nb090_alpha_dummy_722] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv) 0

theorem nb090_fresh_099 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_746 v u h) ∉ (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_746] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_100 (A : Class) : (nb090_alpha_dummy_781 A) ∉ (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) := by
  simpa only [nb090_alpha_dummy_781] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) 0

theorem nb090_fresh_101 (A : Class) : (nb090_alpha_dummy_782 A) ∉ (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) := by
  simpa only [nb090_alpha_dummy_782] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) 1

theorem nb090_distinct_102 (A : Class) : (nb090_alpha_dummy_781 A) ≠ (nb090_alpha_dummy_782 A) := by
  simpa only [nb090_alpha_dummy_781, nb090_alpha_dummy_782] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A) (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_103 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_783 v u h) ∉ (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) := by
  simpa only [nb090_alpha_dummy_783] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) 0

theorem nb090_fresh_104 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_784 v u h) ∉ (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) := by
  simpa only [nb090_alpha_dummy_784] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) 1

theorem nb090_distinct_105 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_783 v u h) ≠ (nb090_alpha_dummy_784 v u h) := by
  simpa only [nb090_alpha_dummy_783, nb090_alpha_dummy_784] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq (Class.cab (nb090_alpha_dummy_778 v u h) (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))) (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_106 (A : Class) : (nb090_alpha_dummy_791 A) ∉ (((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_791] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv) 0

theorem nb090_fresh_107 (A : Class) : (nb090_alpha_dummy_815 A) ∉ (((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_815] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A) (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_108 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_792 v u h) ∉ (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv) := by
  simpa only [nb090_alpha_dummy_792] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv) 0

theorem nb090_fresh_109 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_816 v u h) ∉ (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_816] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_110 (A : Class) : (nb090_alpha_dummy_831 A) ∉ (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) := by
  simpa only [nb090_alpha_dummy_831] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) 0

theorem nb090_fresh_111 (A : Class) : (nb090_alpha_dummy_832 A) ∉ (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) := by
  simpa only [nb090_alpha_dummy_832] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) 1

theorem nb090_distinct_112 (A : Class) : (nb090_alpha_dummy_831 A) ≠ (nb090_alpha_dummy_832 A) := by
  simpa only [nb090_alpha_dummy_831, nb090_alpha_dummy_832] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_113 (v : Var) : (nb090_alpha_dummy_833 v) ∉ (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) := by
  simpa only [nb090_alpha_dummy_833] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) 0

theorem nb090_fresh_114 (v : Var) : (nb090_alpha_dummy_834 v) ∉ (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) := by
  simpa only [nb090_alpha_dummy_834] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) 1

theorem nb090_distinct_115 (v : Var) : (nb090_alpha_dummy_833 v) ≠ (nb090_alpha_dummy_834 v) := by
  simpa only [nb090_alpha_dummy_833, nb090_alpha_dummy_834] using
    (freshVar_injective (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v) (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_116 (A : Class) : (nb090_alpha_dummy_841 A) ∉ (((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_841] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv) 0

theorem nb090_fresh_117 (A : Class) : (nb090_alpha_dummy_865 A) ∉ (((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_865] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A) (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_118 (v : Var) : (nb090_alpha_dummy_866 v) ∉ (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb090_alpha_dummy_866] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb090_fresh_119 (v : Var) : (nb090_alpha_dummy_842 v) ∉ (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv) := by
  simpa only [nb090_alpha_dummy_842] using freshVar_not_mem (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv) 0

theorem nb090_fresh_120 (A : Class) : (nb090_alpha_dummy_129 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv) := by
  simpa only [nb090_alpha_dummy_129] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv) 0

theorem nb090_fresh_121 (A : Class) : (nb090_alpha_dummy_130 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv) := by
  simpa only [nb090_alpha_dummy_130] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv) 1

theorem nb090_distinct_122 (A : Class) : (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_130 A) := by
  simpa only [nb090_alpha_dummy_129, nb090_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_123 (A : Class) : (nb090_alpha_dummy_707 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_041 A))).fv) := by
  simpa only [nb090_alpha_dummy_707] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_041 A))).fv) 0

theorem nb090_fresh_124 (A : Class) : (nb090_alpha_dummy_777 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) := by
  simpa only [nb090_alpha_dummy_777] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) 0

theorem nb090_fresh_125 (A : Class) : (nb090_alpha_dummy_049 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) := by
  simpa only [nb090_alpha_dummy_049] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 0

theorem nb090_fresh_126 (A : Class) : (nb090_alpha_dummy_050 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) := by
  simpa only [nb090_alpha_dummy_050] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 1

theorem nb090_fresh_127 (A : Class) : (nb090_alpha_dummy_051 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) := by
  simpa only [nb090_alpha_dummy_051] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 2

theorem nb090_distinct_128 (A : Class) : (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_050 A) := by
  simpa only [nb090_alpha_dummy_049, nb090_alpha_dummy_050] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_129 (A : Class) : (nb090_alpha_dummy_049 A) ≠ (nb090_alpha_dummy_051 A) := by
  simpa only [nb090_alpha_dummy_049, nb090_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_130 (A : Class) : (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_051 A) := by
  simpa only [nb090_alpha_dummy_050, nb090_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_131 (A : Class) : (nb090_alpha_dummy_041 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) := by
  simpa only [nb090_alpha_dummy_041] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) 0

theorem nb090_fresh_132 (A : Class) : (nb090_alpha_dummy_042 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) := by
  simpa only [nb090_alpha_dummy_042] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) 1

theorem nb090_distinct_133 (A : Class) : (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_042 A) := by
  simpa only [nb090_alpha_dummy_041, nb090_alpha_dummy_042] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_134 (A : Class) : (nb090_alpha_dummy_333 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb090_alpha_dummy_333] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) 0

theorem nb090_fresh_135 (A : Class) : (nb090_alpha_dummy_334 A) ∉ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb090_alpha_dummy_334] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) 1

theorem nb090_distinct_136 (A : Class) : (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_334 A) := by
  simpa only [nb090_alpha_dummy_333, nb090_alpha_dummy_334] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_137 (A : Class) : (nb090_alpha_dummy_005 A) ∉ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) := by
  simpa only [nb090_alpha_dummy_005] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0

theorem nb090_fresh_138 (A : Class) : (nb090_alpha_dummy_006 A) ∉ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) := by
  simpa only [nb090_alpha_dummy_006] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 1

theorem nb090_distinct_139 (A : Class) : (nb090_alpha_dummy_005 A) ≠ (nb090_alpha_dummy_006 A) := by
  simpa only [nb090_alpha_dummy_005, nb090_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_140 (A : Class) : (nb090_alpha_dummy_291 A) ∉ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) := by
  simpa only [nb090_alpha_dummy_291] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) 0

theorem nb090_fresh_141 (A : Class) : (nb090_alpha_dummy_292 A) ∉ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) := by
  simpa only [nb090_alpha_dummy_292] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) 1

theorem nb090_distinct_142 (A : Class) : (nb090_alpha_dummy_291 A) ≠ (nb090_alpha_dummy_292 A) := by
  simpa only [nb090_alpha_dummy_291, nb090_alpha_dummy_292] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_143 (A : Class) : (nb090_alpha_dummy_661 A) ∉ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) := by
  simpa only [nb090_alpha_dummy_661] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) 0

theorem nb090_fresh_144 (A : Class) : (nb090_alpha_dummy_662 A) ∉ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) := by
  simpa only [nb090_alpha_dummy_662] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) 1

theorem nb090_distinct_145 (A : Class) : (nb090_alpha_dummy_661 A) ≠ (nb090_alpha_dummy_662 A) := by
  simpa only [nb090_alpha_dummy_661, nb090_alpha_dummy_662] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_146 (A : Class) : (nb090_alpha_dummy_381 A) ∉ (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) := by
  simpa only [nb090_alpha_dummy_381] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) 0

theorem nb090_fresh_147 (A : Class) : (nb090_alpha_dummy_382 A) ∉ (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) := by
  simpa only [nb090_alpha_dummy_382] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) 1

theorem nb090_distinct_148 (A : Class) : (nb090_alpha_dummy_381 A) ≠ (nb090_alpha_dummy_382 A) := by
  simpa only [nb090_alpha_dummy_381, nb090_alpha_dummy_382] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_149 (A : Class) : (nb090_alpha_dummy_835 A) ∉ (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) := by
  simpa only [nb090_alpha_dummy_835] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) 0

theorem nb090_fresh_150 (A : Class) : (nb090_alpha_dummy_836 A) ∉ (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) := by
  simpa only [nb090_alpha_dummy_836] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) 1

theorem nb090_distinct_151 (A : Class) : (nb090_alpha_dummy_835 A) ≠ (nb090_alpha_dummy_836 A) := by
  simpa only [nb090_alpha_dummy_835, nb090_alpha_dummy_836] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_152 (A : Class) : (nb090_alpha_dummy_013 A) ∉ (((Class.cv (nb090_alpha_dummy_006 A))).fv) := by
  simpa only [nb090_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_006 A))).fv) 0

theorem nb090_fresh_153 (A : Class) : (nb090_alpha_dummy_014 A) ∉ (((Class.cv (nb090_alpha_dummy_006 A))).fv) := by
  simpa only [nb090_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_006 A))).fv) 1

theorem nb090_distinct_154 (A : Class) : (nb090_alpha_dummy_013 A) ≠ (nb090_alpha_dummy_014 A) := by
  simpa only [nb090_alpha_dummy_013, nb090_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_006 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_155 (v : Var) (u : Var) : (nb090_alpha_dummy_015 v u) ∉ (((Class.cv (nb090_alpha_dummy_008 v u))).fv) := by
  simpa only [nb090_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_008 v u))).fv) 0

theorem nb090_fresh_156 (v : Var) (u : Var) : (nb090_alpha_dummy_016 v u) ∉ (((Class.cv (nb090_alpha_dummy_008 v u))).fv) := by
  simpa only [nb090_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_008 v u))).fv) 1

theorem nb090_distinct_157 (v : Var) (u : Var) : (nb090_alpha_dummy_015 v u) ≠ (nb090_alpha_dummy_016 v u) := by
  simpa only [nb090_alpha_dummy_015, nb090_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_008 v u))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_158 (A : Class) : (nb090_alpha_dummy_019 A) ∉ (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_159 (A : Class) : (nb090_alpha_dummy_020 A) ∉ (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_160 (A : Class) : (nb090_alpha_dummy_021 A) ∉ (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_161 (A : Class) : (nb090_alpha_dummy_019 A) ≠ (nb090_alpha_dummy_020 A) := by
  simpa only [nb090_alpha_dummy_019, nb090_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_162 (A : Class) : (nb090_alpha_dummy_019 A) ≠ (nb090_alpha_dummy_021 A) := by
  simpa only [nb090_alpha_dummy_019, nb090_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_163 (A : Class) : (nb090_alpha_dummy_020 A) ≠ (nb090_alpha_dummy_021 A) := by
  simpa only [nb090_alpha_dummy_020, nb090_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_164 (v : Var) (u : Var) : (nb090_alpha_dummy_022 v u) ∉ (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_165 (v : Var) (u : Var) : (nb090_alpha_dummy_023 v u) ∉ (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_166 (v : Var) (u : Var) : (nb090_alpha_dummy_024 v u) ∉ (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_167 (v : Var) (u : Var) : (nb090_alpha_dummy_022 v u) ≠ (nb090_alpha_dummy_023 v u) := by
  simpa only [nb090_alpha_dummy_022, nb090_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_168 (v : Var) (u : Var) : (nb090_alpha_dummy_022 v u) ≠ (nb090_alpha_dummy_024 v u) := by
  simpa only [nb090_alpha_dummy_022, nb090_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_169 (v : Var) (u : Var) : (nb090_alpha_dummy_023 v u) ≠ (nb090_alpha_dummy_024 v u) := by
  simpa only [nb090_alpha_dummy_023, nb090_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_170 (A : Class) : (nb090_alpha_dummy_031 A) ∉ (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_020 A))).fv) := by
  simpa only [nb090_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_020 A))).fv) 0

theorem nb090_fresh_171 (A : Class) : (nb090_alpha_dummy_027 A) ∉ (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) := by
  simpa only [nb090_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) 0

theorem nb090_fresh_172 (A : Class) : (nb090_alpha_dummy_033 A) ∉ (((Class.cv (nb090_alpha_dummy_021 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) := by
  simpa only [nb090_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_021 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) 0

theorem nb090_fresh_173 (v : Var) (u : Var) : (nb090_alpha_dummy_032 v u) ∉ (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_023 v u))).fv) := by
  simpa only [nb090_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_023 v u))).fv) 0

theorem nb090_fresh_174 (v : Var) (u : Var) : (nb090_alpha_dummy_028 v u) ∉ (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_024 v u))).fv) := by
  simpa only [nb090_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_024 v u))).fv) 0

theorem nb090_fresh_175 (v : Var) (u : Var) : (nb090_alpha_dummy_034 v u) ∉ (((Class.cv (nb090_alpha_dummy_024 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_024 v u))).fv) := by
  simpa only [nb090_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_024 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_024 v u))).fv) 0

theorem nb090_fresh_176 (A : Class) : (nb090_alpha_dummy_617 A) ∉ (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) := by
  simpa only [nb090_alpha_dummy_617] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) 0

theorem nb090_fresh_177 (A : Class) : (nb090_alpha_dummy_618 A) ∉ (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) := by
  simpa only [nb090_alpha_dummy_618] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) 1

theorem nb090_distinct_178 (A : Class) : (nb090_alpha_dummy_617 A) ≠ (nb090_alpha_dummy_618 A) := by
  simpa only [nb090_alpha_dummy_617, nb090_alpha_dummy_618] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_179 (A : Class) : (nb090_alpha_dummy_715 A) ∉ (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) := by
  simpa only [nb090_alpha_dummy_715] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) 0

theorem nb090_fresh_180 (A : Class) : (nb090_alpha_dummy_716 A) ∉ (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) := by
  simpa only [nb090_alpha_dummy_716] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) 1

theorem nb090_distinct_181 (A : Class) : (nb090_alpha_dummy_715 A) ≠ (nb090_alpha_dummy_716 A) := by
  simpa only [nb090_alpha_dummy_715, nb090_alpha_dummy_716] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_182 (A : Class) : (nb090_alpha_dummy_785 A) ∉ (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) := by
  simpa only [nb090_alpha_dummy_785] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) 0

theorem nb090_fresh_183 (A : Class) : (nb090_alpha_dummy_786 A) ∉ (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) := by
  simpa only [nb090_alpha_dummy_786] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) 1

theorem nb090_distinct_184 (A : Class) : (nb090_alpha_dummy_785 A) ≠ (nb090_alpha_dummy_786 A) := by
  simpa only [nb090_alpha_dummy_785, nb090_alpha_dummy_786] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_185 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_619 v u h) ∉ (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_619] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 0

theorem nb090_fresh_186 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_620 v u h) ∉ (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_620] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 1

theorem nb090_distinct_187 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_619 v u h) ≠ (nb090_alpha_dummy_620 v u h) := by
  simpa only [nb090_alpha_dummy_619, nb090_alpha_dummy_620] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_188 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_717 v u h) ∉ (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_717] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) 0

theorem nb090_fresh_189 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_718 v u h) ∉ (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_718] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) 1

theorem nb090_distinct_190 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_717 v u h) ≠ (nb090_alpha_dummy_718 v u h) := by
  simpa only [nb090_alpha_dummy_717, nb090_alpha_dummy_718] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_191 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_787 v u h) ∉ (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_787] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) 0

theorem nb090_fresh_192 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_788 v u h) ∉ (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) := by
  simpa only [nb090_alpha_dummy_788] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) 1

theorem nb090_distinct_193 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_787 v u h) ≠ (nb090_alpha_dummy_788 v u h) := by
  simpa only [nb090_alpha_dummy_787, nb090_alpha_dummy_788] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪ ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_194 (A : Class) : (nb090_alpha_dummy_057 A) ∉ (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) := by
  simpa only [nb090_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) 0

theorem nb090_fresh_195 (A : Class) : (nb090_alpha_dummy_058 A) ∉ (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) := by
  simpa only [nb090_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) 1

theorem nb090_distinct_196 (A : Class) : (nb090_alpha_dummy_057 A) ≠ (nb090_alpha_dummy_058 A) := by
  simpa only [nb090_alpha_dummy_057, nb090_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_197 (A : Class) : (nb090_alpha_dummy_093 A) ∉ (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) := by
  simpa only [nb090_alpha_dummy_093] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) 0

theorem nb090_fresh_198 (A : Class) : (nb090_alpha_dummy_094 A) ∉ (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) := by
  simpa only [nb090_alpha_dummy_094] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) 1

theorem nb090_distinct_199 (A : Class) : (nb090_alpha_dummy_093 A) ≠ (nb090_alpha_dummy_094 A) := by
  simpa only [nb090_alpha_dummy_093, nb090_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_051 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_200 (A : Class) : (nb090_alpha_dummy_207 A) ∉ (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) := by
  simpa only [nb090_alpha_dummy_207] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) 0

theorem nb090_fresh_201 (A : Class) : (nb090_alpha_dummy_208 A) ∉ (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) := by
  simpa only [nb090_alpha_dummy_208] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) 1

theorem nb090_distinct_202 (A : Class) : (nb090_alpha_dummy_207 A) ≠ (nb090_alpha_dummy_208 A) := by
  simpa only [nb090_alpha_dummy_207, nb090_alpha_dummy_208] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_203 (h : Var) : (nb090_alpha_dummy_059 h) ∉ (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) := by
  simpa only [nb090_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) 0

theorem nb090_fresh_204 (h : Var) : (nb090_alpha_dummy_060 h) ∉ (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) := by
  simpa only [nb090_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) 1

theorem nb090_distinct_205 (h : Var) : (nb090_alpha_dummy_059 h) ≠ (nb090_alpha_dummy_060 h) := by
  simpa only [nb090_alpha_dummy_059, nb090_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_206 (h : Var) : (nb090_alpha_dummy_095 h) ∉ (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) := by
  simpa only [nb090_alpha_dummy_095] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) 0

theorem nb090_fresh_207 (h : Var) : (nb090_alpha_dummy_096 h) ∉ (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) := by
  simpa only [nb090_alpha_dummy_096] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) 1

theorem nb090_distinct_208 (h : Var) : (nb090_alpha_dummy_095 h) ≠ (nb090_alpha_dummy_096 h) := by
  simpa only [nb090_alpha_dummy_095, nb090_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_054 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_209 (h : Var) : (nb090_alpha_dummy_209 h) ∉ (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) := by
  simpa only [nb090_alpha_dummy_209] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) 0

theorem nb090_fresh_210 (h : Var) : (nb090_alpha_dummy_210 h) ∉ (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) := by
  simpa only [nb090_alpha_dummy_210] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) 1

theorem nb090_distinct_211 (h : Var) : (nb090_alpha_dummy_209 h) ≠ (nb090_alpha_dummy_210 h) := by
  simpa only [nb090_alpha_dummy_209, nb090_alpha_dummy_210] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_212 (A : Class) : (nb090_alpha_dummy_065 A) ∉ (((Class.cv (nb090_alpha_dummy_058 A))).fv) := by
  simpa only [nb090_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_058 A))).fv) 0

theorem nb090_fresh_213 (A : Class) : (nb090_alpha_dummy_066 A) ∉ (((Class.cv (nb090_alpha_dummy_058 A))).fv) := by
  simpa only [nb090_alpha_dummy_066] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_058 A))).fv) 1

theorem nb090_distinct_214 (A : Class) : (nb090_alpha_dummy_065 A) ≠ (nb090_alpha_dummy_066 A) := by
  simpa only [nb090_alpha_dummy_065, nb090_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_058 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_215 (h : Var) : (nb090_alpha_dummy_067 h) ∉ (((Class.cv (nb090_alpha_dummy_060 h))).fv) := by
  simpa only [nb090_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_060 h))).fv) 0

theorem nb090_fresh_216 (h : Var) : (nb090_alpha_dummy_068 h) ∉ (((Class.cv (nb090_alpha_dummy_060 h))).fv) := by
  simpa only [nb090_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_060 h))).fv) 1

theorem nb090_distinct_217 (h : Var) : (nb090_alpha_dummy_067 h) ≠ (nb090_alpha_dummy_068 h) := by
  simpa only [nb090_alpha_dummy_067, nb090_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_060 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_218 (A : Class) : (nb090_alpha_dummy_071 A) ∉ (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_219 (A : Class) : (nb090_alpha_dummy_072 A) ∉ (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_220 (A : Class) : (nb090_alpha_dummy_073 A) ∉ (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_073] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_221 (A : Class) : (nb090_alpha_dummy_071 A) ≠ (nb090_alpha_dummy_072 A) := by
  simpa only [nb090_alpha_dummy_071, nb090_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_222 (A : Class) : (nb090_alpha_dummy_071 A) ≠ (nb090_alpha_dummy_073 A) := by
  simpa only [nb090_alpha_dummy_071, nb090_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_223 (A : Class) : (nb090_alpha_dummy_072 A) ≠ (nb090_alpha_dummy_073 A) := by
  simpa only [nb090_alpha_dummy_072, nb090_alpha_dummy_073] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_224 (h : Var) : (nb090_alpha_dummy_074 h) ∉ (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_074] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 0

theorem nb090_fresh_225 (h : Var) : (nb090_alpha_dummy_075 h) ∉ (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_075] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 1

theorem nb090_fresh_226 (h : Var) : (nb090_alpha_dummy_076 h) ∉ (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb090_alpha_dummy_076] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 2

theorem nb090_distinct_227 (h : Var) : (nb090_alpha_dummy_074 h) ≠ (nb090_alpha_dummy_075 h) := by
  simpa only [nb090_alpha_dummy_074, nb090_alpha_dummy_075] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_228 (h : Var) : (nb090_alpha_dummy_074 h) ≠ (nb090_alpha_dummy_076 h) := by
  simpa only [nb090_alpha_dummy_074, nb090_alpha_dummy_076] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_229 (h : Var) : (nb090_alpha_dummy_075 h) ≠ (nb090_alpha_dummy_076 h) := by
  simpa only [nb090_alpha_dummy_075, nb090_alpha_dummy_076] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_230 (A : Class) : (nb090_alpha_dummy_083 A) ∉ (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_072 A))).fv) := by
  simpa only [nb090_alpha_dummy_083] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_072 A))).fv) 0

theorem nb090_fresh_231 (A : Class) : (nb090_alpha_dummy_079 A) ∉ (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) := by
  simpa only [nb090_alpha_dummy_079] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) 0

theorem nb090_fresh_232 (A : Class) : (nb090_alpha_dummy_085 A) ∉ (((Class.cv (nb090_alpha_dummy_073 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) := by
  simpa only [nb090_alpha_dummy_085] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_073 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) 0

theorem nb090_fresh_233 (h : Var) : (nb090_alpha_dummy_084 h) ∉ (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_075 h))).fv) := by
  simpa only [nb090_alpha_dummy_084] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_075 h))).fv) 0

theorem nb090_fresh_234 (h : Var) : (nb090_alpha_dummy_080 h) ∉ (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) := by
  simpa only [nb090_alpha_dummy_080] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) 0

theorem nb090_fresh_235 (h : Var) : (nb090_alpha_dummy_086 h) ∉ (((Class.cv (nb090_alpha_dummy_076 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) := by
  simpa only [nb090_alpha_dummy_086] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_076 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) 0

theorem nb090_fresh_236 (A : Class) : (nb090_alpha_dummy_101 A) ∉ (((Class.cv (nb090_alpha_dummy_094 A))).fv) := by
  simpa only [nb090_alpha_dummy_101] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_094 A))).fv) 0

theorem nb090_fresh_237 (A : Class) : (nb090_alpha_dummy_102 A) ∉ (((Class.cv (nb090_alpha_dummy_094 A))).fv) := by
  simpa only [nb090_alpha_dummy_102] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_094 A))).fv) 1

theorem nb090_distinct_238 (A : Class) : (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_102 A) := by
  simpa only [nb090_alpha_dummy_101, nb090_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_094 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_239 (h : Var) : (nb090_alpha_dummy_103 h) ∉ (((Class.cv (nb090_alpha_dummy_096 h))).fv) := by
  simpa only [nb090_alpha_dummy_103] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_096 h))).fv) 0

theorem nb090_fresh_240 (h : Var) : (nb090_alpha_dummy_104 h) ∉ (((Class.cv (nb090_alpha_dummy_096 h))).fv) := by
  simpa only [nb090_alpha_dummy_104] using freshVar_not_mem (((Class.cv (nb090_alpha_dummy_096 h))).fv) 1

theorem nb090_distinct_241 (h : Var) : (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_104 h) := by
  simpa only [nb090_alpha_dummy_103, nb090_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb090_alpha_dummy_096 h))).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
