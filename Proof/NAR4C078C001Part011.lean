import NAR4C078C001Part010

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

theorem nb078_fresh_104 : (nb078_alpha_dummy_817) ∉ (((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv) := by
  simpa only [nb078_alpha_dummy_817] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv) 0

theorem nb078_fresh_105 : (nb078_alpha_dummy_841) ∉ (((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_841] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811) (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_811)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_106 (h : Var) : (nb078_alpha_dummy_818 h) ∉ (((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv) := by
  simpa only [nb078_alpha_dummy_818] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv) 0

theorem nb078_fresh_107 (h : Var) : (nb078_alpha_dummy_842 h) ∉ (((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_842] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h) (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_108 : (nb078_alpha_dummy_859) ∉ (((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv) := by
  simpa only [nb078_alpha_dummy_859] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv) 0

theorem nb078_fresh_109 : (nb078_alpha_dummy_883) ∉ (((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_883] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853) (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_853)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_110 (h : Var) : (nb078_alpha_dummy_860 h) ∉ (((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv) := by
  simpa only [nb078_alpha_dummy_860] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv) 0

theorem nb078_fresh_111 (h : Var) : (nb078_alpha_dummy_884 h) ∉ (((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_884] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h) (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_112 : (nb078_alpha_dummy_919) ∉ (((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_919] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_113 : (nb078_alpha_dummy_895) ∉ (((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv) := by
  simpa only [nb078_alpha_dummy_895] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv) 0

theorem nb078_fresh_114 (h : Var) : (nb078_alpha_dummy_920 h) ∉ (((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_920] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_115 (h : Var) : (nb078_alpha_dummy_896 h) ∉ (((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv) := by
  simpa only [nb078_alpha_dummy_896] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv) 0

theorem nb078_fresh_116 : (nb078_alpha_dummy_955) ∉ (((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_955] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_117 : (nb078_alpha_dummy_931) ∉ (((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv) := by
  simpa only [nb078_alpha_dummy_931] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv) 0

theorem nb078_fresh_118 (h : Var) : (nb078_alpha_dummy_956 h) ∉ (((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_956] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_119 (h : Var) : (nb078_alpha_dummy_932 h) ∉ (((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv) := by
  simpa only [nb078_alpha_dummy_932] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv) 0

theorem nb078_fresh_120 : (nb078_alpha_dummy_995) ∉ (((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_995] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_121 : (nb078_alpha_dummy_971) ∉ (((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv) := by
  simpa only [nb078_alpha_dummy_971] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv) 0

theorem nb078_fresh_122 (h : Var) : (nb078_alpha_dummy_996 h) ∉ (((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb078_alpha_dummy_996] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb078_fresh_123 (h : Var) : (nb078_alpha_dummy_972 h) ∉ (((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv) := by
  simpa only [nb078_alpha_dummy_972] using freshVar_not_mem (((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv) 0

theorem nb078_fresh_124 : (nb078_alpha_dummy_089) ∉ (((Class.cv (nb078_alpha_dummy_000))).fv) := by
  simpa only [nb078_alpha_dummy_089] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv) 0

theorem nb078_fresh_125 : (nb078_alpha_dummy_090) ∉ (((Class.cv (nb078_alpha_dummy_000))).fv) := by
  simpa only [nb078_alpha_dummy_090] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv) 1

theorem nb078_distinct_126 : (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_090) := by
  simpa only [nb078_alpha_dummy_089, nb078_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_127 : (nb078_alpha_dummy_009) ∉ (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) := by
  simpa only [nb078_alpha_dummy_009] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) 0

theorem nb078_fresh_128 : (nb078_alpha_dummy_010) ∉ (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) := by
  simpa only [nb078_alpha_dummy_010] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) 1

theorem nb078_fresh_129 : (nb078_alpha_dummy_011) ∉ (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) := by
  simpa only [nb078_alpha_dummy_011] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) 2

theorem nb078_distinct_130 : (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_010) := by
  simpa only [nb078_alpha_dummy_009, nb078_alpha_dummy_010] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_131 : (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_011) := by
  simpa only [nb078_alpha_dummy_009, nb078_alpha_dummy_011] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_132 : (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_011) := by
  simpa only [nb078_alpha_dummy_010, nb078_alpha_dummy_011] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_133 : (nb078_alpha_dummy_243) ∉ (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_243] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_134 : (nb078_alpha_dummy_244) ∉ (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_244] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_135 : (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_244) := by
  simpa only [nb078_alpha_dummy_243, nb078_alpha_dummy_244] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_136 : (nb078_alpha_dummy_367) ∉ (((Class.cv (nb078_alpha_dummy_001))).fv) := by
  simpa only [nb078_alpha_dummy_367] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv) 0

theorem nb078_fresh_137 : (nb078_alpha_dummy_368) ∉ (((Class.cv (nb078_alpha_dummy_001))).fv) := by
  simpa only [nb078_alpha_dummy_368] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv) 1

theorem nb078_distinct_138 : (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_368) := by
  simpa only [nb078_alpha_dummy_367, nb078_alpha_dummy_368] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_139 : (nb078_alpha_dummy_287) ∉ (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) := by
  simpa only [nb078_alpha_dummy_287] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 0

theorem nb078_fresh_140 : (nb078_alpha_dummy_288) ∉ (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) := by
  simpa only [nb078_alpha_dummy_288] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 1

theorem nb078_fresh_141 : (nb078_alpha_dummy_289) ∉ (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) := by
  simpa only [nb078_alpha_dummy_289] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) 2

theorem nb078_distinct_142 : (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_288) := by
  simpa only [nb078_alpha_dummy_287, nb078_alpha_dummy_288] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_143 : (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_289) := by
  simpa only [nb078_alpha_dummy_287, nb078_alpha_dummy_289] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_144 : (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_289) := by
  simpa only [nb078_alpha_dummy_288, nb078_alpha_dummy_289] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_145 : (nb078_alpha_dummy_525) ∉ (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_525] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_146 : (nb078_alpha_dummy_526) ∉ (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_526] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_147 : (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_526) := by
  simpa only [nb078_alpha_dummy_525, nb078_alpha_dummy_526] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_148 : (nb078_alpha_dummy_847) ∉ (((Class.cv (nb078_alpha_dummy_002))).fv) := by
  simpa only [nb078_alpha_dummy_847] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv) 0

theorem nb078_fresh_149 : (nb078_alpha_dummy_848) ∉ (((Class.cv (nb078_alpha_dummy_002))).fv) := by
  simpa only [nb078_alpha_dummy_848] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv) 1

theorem nb078_distinct_150 : (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_848) := by
  simpa only [nb078_alpha_dummy_847, nb078_alpha_dummy_848] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_151 : (nb078_alpha_dummy_767) ∉ (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) := by
  simpa only [nb078_alpha_dummy_767] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 0

theorem nb078_fresh_152 : (nb078_alpha_dummy_768) ∉ (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) := by
  simpa only [nb078_alpha_dummy_768] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 1

theorem nb078_fresh_153 : (nb078_alpha_dummy_769) ∉ (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) := by
  simpa only [nb078_alpha_dummy_769] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 2

theorem nb078_distinct_154 : (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_768) := by
  simpa only [nb078_alpha_dummy_767, nb078_alpha_dummy_768] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_155 : (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_769) := by
  simpa only [nb078_alpha_dummy_767, nb078_alpha_dummy_769] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_156 : (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_769) := by
  simpa only [nb078_alpha_dummy_768, nb078_alpha_dummy_769] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_157 : (nb078_alpha_dummy_1005) ∉ (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_1005] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_158 : (nb078_alpha_dummy_1006) ∉ (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb078_alpha_dummy_1006] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_159 : (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1006) := by
  simpa only [nb078_alpha_dummy_1005, nb078_alpha_dummy_1006] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_160 : (nb078_alpha_dummy_017) ∉ (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) := by
  simpa only [nb078_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 0

theorem nb078_fresh_161 : (nb078_alpha_dummy_018) ∉ (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) := by
  simpa only [nb078_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 1

theorem nb078_distinct_162 : (nb078_alpha_dummy_017) ≠ (nb078_alpha_dummy_018) := by
  simpa only [nb078_alpha_dummy_017, nb078_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_163 : (nb078_alpha_dummy_053) ∉ (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) := by
  simpa only [nb078_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) 0

theorem nb078_fresh_164 : (nb078_alpha_dummy_054) ∉ (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) := by
  simpa only [nb078_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) 1

theorem nb078_distinct_165 : (nb078_alpha_dummy_053) ≠ (nb078_alpha_dummy_054) := by
  simpa only [nb078_alpha_dummy_053, nb078_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_166 : (nb078_alpha_dummy_167) ∉ (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) := by
  simpa only [nb078_alpha_dummy_167] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 0

theorem nb078_fresh_167 : (nb078_alpha_dummy_168) ∉ (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) := by
  simpa only [nb078_alpha_dummy_168] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) 1

theorem nb078_distinct_168 : (nb078_alpha_dummy_167) ≠ (nb078_alpha_dummy_168) := by
  simpa only [nb078_alpha_dummy_167, nb078_alpha_dummy_168] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_169 (f : Var) : (nb078_alpha_dummy_019 f) ∉ (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) := by
  simpa only [nb078_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) 0

theorem nb078_fresh_170 (f : Var) : (nb078_alpha_dummy_020 f) ∉ (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) := by
  simpa only [nb078_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) 1

theorem nb078_distinct_171 (f : Var) : (nb078_alpha_dummy_019 f) ≠ (nb078_alpha_dummy_020 f) := by
  simpa only [nb078_alpha_dummy_019, nb078_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_172 (f : Var) : (nb078_alpha_dummy_055 f) ∉ (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) := by
  simpa only [nb078_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) 0

theorem nb078_fresh_173 (f : Var) : (nb078_alpha_dummy_056 f) ∉ (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) := by
  simpa only [nb078_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) 1

theorem nb078_distinct_174 (f : Var) : (nb078_alpha_dummy_055 f) ≠ (nb078_alpha_dummy_056 f) := by
  simpa only [nb078_alpha_dummy_055, nb078_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_175 (f : Var) : (nb078_alpha_dummy_169 f) ∉ (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) := by
  simpa only [nb078_alpha_dummy_169] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) 0

theorem nb078_fresh_176 (f : Var) : (nb078_alpha_dummy_170 f) ∉ (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) := by
  simpa only [nb078_alpha_dummy_170] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) 1

theorem nb078_distinct_177 (f : Var) : (nb078_alpha_dummy_169 f) ≠ (nb078_alpha_dummy_170 f) := by
  simpa only [nb078_alpha_dummy_169, nb078_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_178 : (nb078_alpha_dummy_025) ∉ (((Class.cv (nb078_alpha_dummy_018))).fv) := by
  simpa only [nb078_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_018))).fv) 0

theorem nb078_fresh_179 : (nb078_alpha_dummy_026) ∉ (((Class.cv (nb078_alpha_dummy_018))).fv) := by
  simpa only [nb078_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_018))).fv) 1

theorem nb078_distinct_180 : (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_026) := by
  simpa only [nb078_alpha_dummy_025, nb078_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_018))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_181 (f : Var) : (nb078_alpha_dummy_027 f) ∉ (((Class.cv (nb078_alpha_dummy_020 f))).fv) := by
  simpa only [nb078_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_020 f))).fv) 0

theorem nb078_fresh_182 (f : Var) : (nb078_alpha_dummy_028 f) ∉ (((Class.cv (nb078_alpha_dummy_020 f))).fv) := by
  simpa only [nb078_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_020 f))).fv) 1

theorem nb078_distinct_183 (f : Var) : (nb078_alpha_dummy_027 f) ≠ (nb078_alpha_dummy_028 f) := by
  simpa only [nb078_alpha_dummy_027, nb078_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_020 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_184 : (nb078_alpha_dummy_031) ∉ (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_185 : (nb078_alpha_dummy_032) ∉ (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_186 : (nb078_alpha_dummy_033) ∉ (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_187 : (nb078_alpha_dummy_031) ≠ (nb078_alpha_dummy_032) := by
  simpa only [nb078_alpha_dummy_031, nb078_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_188 : (nb078_alpha_dummy_031) ≠ (nb078_alpha_dummy_033) := by
  simpa only [nb078_alpha_dummy_031, nb078_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_189 : (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_033) := by
  simpa only [nb078_alpha_dummy_032, nb078_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_190 (f : Var) : (nb078_alpha_dummy_034 f) ∉ (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_191 (f : Var) : (nb078_alpha_dummy_035 f) ∉ (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_035] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_192 (f : Var) : (nb078_alpha_dummy_036 f) ∉ (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_193 (f : Var) : (nb078_alpha_dummy_034 f) ≠ (nb078_alpha_dummy_035 f) := by
  simpa only [nb078_alpha_dummy_034, nb078_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_194 (f : Var) : (nb078_alpha_dummy_034 f) ≠ (nb078_alpha_dummy_036 f) := by
  simpa only [nb078_alpha_dummy_034, nb078_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_195 (f : Var) : (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_036 f) := by
  simpa only [nb078_alpha_dummy_035, nb078_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_196 : (nb078_alpha_dummy_043) ∉ (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_032))).fv) := by
  simpa only [nb078_alpha_dummy_043] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_032))).fv) 0

theorem nb078_fresh_197 : (nb078_alpha_dummy_039) ∉ (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) := by
  simpa only [nb078_alpha_dummy_039] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) 0

theorem nb078_fresh_198 : (nb078_alpha_dummy_045) ∉ (((Class.cv (nb078_alpha_dummy_033))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) := by
  simpa only [nb078_alpha_dummy_045] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_033))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) 0

theorem nb078_fresh_199 (f : Var) : (nb078_alpha_dummy_044 f) ∉ (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_035 f))).fv) := by
  simpa only [nb078_alpha_dummy_044] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_035 f))).fv) 0

theorem nb078_fresh_200 (f : Var) : (nb078_alpha_dummy_040 f) ∉ (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) := by
  simpa only [nb078_alpha_dummy_040] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) 0

theorem nb078_fresh_201 (f : Var) : (nb078_alpha_dummy_046 f) ∉ (((Class.cv (nb078_alpha_dummy_036 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) := by
  simpa only [nb078_alpha_dummy_046] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_036 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) 0

theorem nb078_fresh_202 : (nb078_alpha_dummy_061) ∉ (((Class.cv (nb078_alpha_dummy_054))).fv) := by
  simpa only [nb078_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_054))).fv) 0

theorem nb078_fresh_203 : (nb078_alpha_dummy_062) ∉ (((Class.cv (nb078_alpha_dummy_054))).fv) := by
  simpa only [nb078_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_054))).fv) 1

theorem nb078_distinct_204 : (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_062) := by
  simpa only [nb078_alpha_dummy_061, nb078_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_054))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_205 (f : Var) : (nb078_alpha_dummy_063 f) ∉ (((Class.cv (nb078_alpha_dummy_056 f))).fv) := by
  simpa only [nb078_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_056 f))).fv) 0

theorem nb078_fresh_206 (f : Var) : (nb078_alpha_dummy_064 f) ∉ (((Class.cv (nb078_alpha_dummy_056 f))).fv) := by
  simpa only [nb078_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_056 f))).fv) 1

theorem nb078_distinct_207 (f : Var) : (nb078_alpha_dummy_063 f) ≠ (nb078_alpha_dummy_064 f) := by
  simpa only [nb078_alpha_dummy_063, nb078_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_056 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_208 : (nb078_alpha_dummy_067) ∉ (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_209 : (nb078_alpha_dummy_068) ∉ (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_210 : (nb078_alpha_dummy_069) ∉ (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_211 : (nb078_alpha_dummy_067) ≠ (nb078_alpha_dummy_068) := by
  simpa only [nb078_alpha_dummy_067, nb078_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_212 : (nb078_alpha_dummy_067) ≠ (nb078_alpha_dummy_069) := by
  simpa only [nb078_alpha_dummy_067, nb078_alpha_dummy_069] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_213 : (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_069) := by
  simpa only [nb078_alpha_dummy_068, nb078_alpha_dummy_069] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_214 (f : Var) : (nb078_alpha_dummy_070 f) ∉ (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_215 (f : Var) : (nb078_alpha_dummy_071 f) ∉ (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_216 (f : Var) : (nb078_alpha_dummy_072 f) ∉ (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb078_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_217 (f : Var) : (nb078_alpha_dummy_070 f) ≠ (nb078_alpha_dummy_071 f) := by
  simpa only [nb078_alpha_dummy_070, nb078_alpha_dummy_071] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_218 (f : Var) : (nb078_alpha_dummy_070 f) ≠ (nb078_alpha_dummy_072 f) := by
  simpa only [nb078_alpha_dummy_070, nb078_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_219 (f : Var) : (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_072 f) := by
  simpa only [nb078_alpha_dummy_071, nb078_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_220 : (nb078_alpha_dummy_079) ∉ (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_068))).fv) := by
  simpa only [nb078_alpha_dummy_079] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_068))).fv) 0

theorem nb078_fresh_221 : (nb078_alpha_dummy_075) ∉ (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) := by
  simpa only [nb078_alpha_dummy_075] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) 0

theorem nb078_fresh_222 : (nb078_alpha_dummy_081) ∉ (((Class.cv (nb078_alpha_dummy_069))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) := by
  simpa only [nb078_alpha_dummy_081] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_069))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) 0

theorem nb078_fresh_223 (f : Var) : (nb078_alpha_dummy_080 f) ∉ (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_071 f))).fv) := by
  simpa only [nb078_alpha_dummy_080] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_071 f))).fv) 0

theorem nb078_fresh_224 (f : Var) : (nb078_alpha_dummy_076 f) ∉ (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) := by
  simpa only [nb078_alpha_dummy_076] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) 0

theorem nb078_fresh_225 (f : Var) : (nb078_alpha_dummy_082 f) ∉ (((Class.cv (nb078_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) := by
  simpa only [nb078_alpha_dummy_082] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) 0

theorem nb078_fresh_226 : (nb078_alpha_dummy_095) ∉ (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) := by
  simpa only [nb078_alpha_dummy_095] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) 0

theorem nb078_fresh_227 : (nb078_alpha_dummy_096) ∉ (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) := by
  simpa only [nb078_alpha_dummy_096] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) 1

theorem nb078_distinct_228 : (nb078_alpha_dummy_095) ≠ (nb078_alpha_dummy_096) := by
  simpa only [nb078_alpha_dummy_095, nb078_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_229 : (nb078_alpha_dummy_131) ∉ (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) := by
  simpa only [nb078_alpha_dummy_131] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) 0

theorem nb078_fresh_230 : (nb078_alpha_dummy_132) ∉ (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) := by
  simpa only [nb078_alpha_dummy_132] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) 1

theorem nb078_distinct_231 : (nb078_alpha_dummy_131) ≠ (nb078_alpha_dummy_132) := by
  simpa only [nb078_alpha_dummy_131, nb078_alpha_dummy_132] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_232 (f : Var) : (nb078_alpha_dummy_097 f) ∉ (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) := by
  simpa only [nb078_alpha_dummy_097] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) 0

theorem nb078_fresh_233 (f : Var) : (nb078_alpha_dummy_098 f) ∉ (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) := by
  simpa only [nb078_alpha_dummy_098] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) 1

theorem nb078_distinct_234 (f : Var) : (nb078_alpha_dummy_097 f) ≠ (nb078_alpha_dummy_098 f) := by
  simpa only [nb078_alpha_dummy_097, nb078_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_235 (f : Var) : (nb078_alpha_dummy_133 f) ∉ (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) := by
  simpa only [nb078_alpha_dummy_133] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) 0

theorem nb078_fresh_236 (f : Var) : (nb078_alpha_dummy_134 f) ∉ (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) := by
  simpa only [nb078_alpha_dummy_134] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) 1

theorem nb078_distinct_237 (f : Var) : (nb078_alpha_dummy_133 f) ≠ (nb078_alpha_dummy_134 f) := by
  simpa only [nb078_alpha_dummy_133, nb078_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_238 : (nb078_alpha_dummy_103) ∉ (((Class.cv (nb078_alpha_dummy_096))).fv) := by
  simpa only [nb078_alpha_dummy_103] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_096))).fv) 0

theorem nb078_fresh_239 : (nb078_alpha_dummy_104) ∉ (((Class.cv (nb078_alpha_dummy_096))).fv) := by
  simpa only [nb078_alpha_dummy_104] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_096))).fv) 1

theorem nb078_distinct_240 : (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_104) := by
  simpa only [nb078_alpha_dummy_103, nb078_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_096))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_241 (f : Var) : (nb078_alpha_dummy_105 f) ∉ (((Class.cv (nb078_alpha_dummy_098 f))).fv) := by
  simpa only [nb078_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_098 f))).fv) 0

theorem nb078_fresh_242 (f : Var) : (nb078_alpha_dummy_106 f) ∉ (((Class.cv (nb078_alpha_dummy_098 f))).fv) := by
  simpa only [nb078_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_098 f))).fv) 1

theorem nb078_distinct_243 (f : Var) : (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_106 f) := by
  simpa only [nb078_alpha_dummy_105, nb078_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_098 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_244 : (nb078_alpha_dummy_1009) ∉ (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) := by
  simpa only [nb078_alpha_dummy_1009] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) 0

theorem nb078_fresh_245 : (nb078_alpha_dummy_1010) ∉ (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) := by
  simpa only [nb078_alpha_dummy_1010] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) 1

theorem nb078_distinct_246 : (nb078_alpha_dummy_1009) ≠ (nb078_alpha_dummy_1010) := by
  simpa only [nb078_alpha_dummy_1009, nb078_alpha_dummy_1010] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_247 (h : Var) : (nb078_alpha_dummy_1011 h) ∉ (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) := by
  simpa only [nb078_alpha_dummy_1011] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) 0

theorem nb078_fresh_248 (h : Var) : (nb078_alpha_dummy_1012 h) ∉ (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) := by
  simpa only [nb078_alpha_dummy_1012] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) 1

theorem nb078_distinct_249 (h : Var) : (nb078_alpha_dummy_1011 h) ≠ (nb078_alpha_dummy_1012 h) := by
  simpa only [nb078_alpha_dummy_1011, nb078_alpha_dummy_1012] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_250 : (nb078_alpha_dummy_1017) ∉ (((Class.cv (nb078_alpha_dummy_1010))).fv) := by
  simpa only [nb078_alpha_dummy_1017] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1010))).fv) 0

theorem nb078_fresh_251 : (nb078_alpha_dummy_1018) ∉ (((Class.cv (nb078_alpha_dummy_1010))).fv) := by
  simpa only [nb078_alpha_dummy_1018] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1010))).fv) 1

theorem nb078_distinct_252 : (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1018) := by
  simpa only [nb078_alpha_dummy_1017, nb078_alpha_dummy_1018] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_253 (h : Var) : (nb078_alpha_dummy_1019 h) ∉ (((Class.cv (nb078_alpha_dummy_1012 h))).fv) := by
  simpa only [nb078_alpha_dummy_1019] using freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1012 h))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
