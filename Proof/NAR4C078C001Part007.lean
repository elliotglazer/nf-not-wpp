import NAR4C078C001Part006

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

noncomputable def nb078_alpha_dummy_900 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_892 h))).fv) 1)

noncomputable def nb078_alpha_dummy_901 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_897)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_897)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_897))).fv) 0)

noncomputable def nb078_alpha_dummy_902 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_899 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_899 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_899 h))).fv) 0)

noncomputable def nb078_alpha_dummy_903 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_904 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_905 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_906 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_907 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_908 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_909 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv) 0)

noncomputable def nb078_alpha_dummy_910 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_911 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) 0)

noncomputable def nb078_alpha_dummy_912 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) 0)

noncomputable def nb078_alpha_dummy_913 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv) 0)

noncomputable def nb078_alpha_dummy_914 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_915 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_904))).fv) 0)

noncomputable def nb078_alpha_dummy_916 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_907 h))).fv) 0)

noncomputable def nb078_alpha_dummy_917 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_905))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) 0)

noncomputable def nb078_alpha_dummy_918 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_908 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) 0)

noncomputable def nb078_alpha_dummy_919 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889) (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847)) (Wff.classEq (Class.cv (nb078_alpha_dummy_889)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_920 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h) (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_921 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_890))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_922 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_923 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv) 0)

noncomputable def nb078_alpha_dummy_924 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_925 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 0)

noncomputable def nb078_alpha_dummy_926 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 1)

noncomputable def nb078_alpha_dummy_927 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) 0)

noncomputable def nb078_alpha_dummy_928 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) 1)

noncomputable def nb078_alpha_dummy_929 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_930 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_931 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv) 0)

noncomputable def nb078_alpha_dummy_932 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_933 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_926))).fv) 0)

noncomputable def nb078_alpha_dummy_934 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_926))).fv) 1)

noncomputable def nb078_alpha_dummy_935 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_928 h))).fv) 0)

noncomputable def nb078_alpha_dummy_936 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_928 h))).fv) 1)

noncomputable def nb078_alpha_dummy_937 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_933)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_933)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_933))).fv) 0)

noncomputable def nb078_alpha_dummy_938 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_935 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_935 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_935 h))).fv) 0)

noncomputable def nb078_alpha_dummy_939 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_940 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_941 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_942 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_943 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_944 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_945 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv) 0)

noncomputable def nb078_alpha_dummy_946 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_947 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) 0)

noncomputable def nb078_alpha_dummy_948 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) 0)

noncomputable def nb078_alpha_dummy_949 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv) 0)

noncomputable def nb078_alpha_dummy_950 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_951 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_940))).fv) 0)

noncomputable def nb078_alpha_dummy_952 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_943 h))).fv) 0)

noncomputable def nb078_alpha_dummy_953 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_941))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) 0)

noncomputable def nb078_alpha_dummy_954 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_944 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) 0)

noncomputable def nb078_alpha_dummy_955 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925) (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768)) (Wff.classEq (Class.cv (nb078_alpha_dummy_925)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_956 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h) (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_957 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_958 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_959 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv) 0)

noncomputable def nb078_alpha_dummy_960 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_961 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_962 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_963 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_964 (h : Var) : Var := (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_965 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) 0)

noncomputable def nb078_alpha_dummy_966 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) 1)

noncomputable def nb078_alpha_dummy_967 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) 0)

noncomputable def nb078_alpha_dummy_968 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) 1)

noncomputable def nb078_alpha_dummy_969 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_970 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_971 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv) 0)

noncomputable def nb078_alpha_dummy_972 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_973 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_966))).fv) 0)

noncomputable def nb078_alpha_dummy_974 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_966))).fv) 1)

noncomputable def nb078_alpha_dummy_975 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_968 h))).fv) 0)

noncomputable def nb078_alpha_dummy_976 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_968 h))).fv) 1)

noncomputable def nb078_alpha_dummy_977 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_973)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_973)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_973))).fv) 0)

noncomputable def nb078_alpha_dummy_978 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_975 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_975 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_975 h))).fv) 0)

noncomputable def nb078_alpha_dummy_979 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_980 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_981 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_982 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_983 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_984 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_985 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv) 0)

noncomputable def nb078_alpha_dummy_986 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_987 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) 0)

noncomputable def nb078_alpha_dummy_988 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) 0)

noncomputable def nb078_alpha_dummy_989 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv) 0)

noncomputable def nb078_alpha_dummy_990 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_991 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_980))).fv) 0)

noncomputable def nb078_alpha_dummy_992 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_983 h))).fv) 0)

noncomputable def nb078_alpha_dummy_993 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_981))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) 0)

noncomputable def nb078_alpha_dummy_994 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_984 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) 0)

noncomputable def nb078_alpha_dummy_995 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965) (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961)) (Wff.classEq (Class.cv (nb078_alpha_dummy_965)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_996 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h) (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_997 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_966))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_998 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_999 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv) 0)

noncomputable def nb078_alpha_dummy_1000 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1001 : Var := (freshVar (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002))) (Class.cv (nb078_alpha_dummy_004)))).fv) 0)

noncomputable def nb078_alpha_dummy_1002 (y : Var) (h : Var) : Var := (freshVar (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv) 0)

noncomputable def nb078_alpha_dummy_1003 : Var := (freshVar (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((Class.cv (nb078_alpha_dummy_004))).fv) 0)

noncomputable def nb078_alpha_dummy_1004 (y : Var) (h : Var) : Var := (freshVar (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) 0)

noncomputable def nb078_alpha_dummy_1005 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_1006 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_1007 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 0)

noncomputable def nb078_alpha_dummy_1008 (h : Var) : Var := (freshVar (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 1)

noncomputable def nb078_alpha_dummy_1009 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) 0)

noncomputable def nb078_alpha_dummy_1010 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) 1)

noncomputable def nb078_alpha_dummy_1011 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1012 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1013 : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1014 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1015 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1016 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1017 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1010))).fv) 0)

noncomputable def nb078_alpha_dummy_1018 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1010))).fv) 1)

noncomputable def nb078_alpha_dummy_1019 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1012 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1020 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1012 h))).fv) 1)

noncomputable def nb078_alpha_dummy_1021 : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1017)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1017)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1017))).fv) 0)

noncomputable def nb078_alpha_dummy_1022 (h : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1019 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_1019 h)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_1019 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1023 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1024 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1025 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1026 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb078_alpha_dummy_1027 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb078_alpha_dummy_1028 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb078_alpha_dummy_1029 : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv) 0)

noncomputable def nb078_alpha_dummy_1030 (h : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h)) (Class.cv (nb078_alpha_dummy_1028 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1031 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) 0)

noncomputable def nb078_alpha_dummy_1032 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1033 : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1024)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1025)))).fv) 0)

noncomputable def nb078_alpha_dummy_1034 (h : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1027 h)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_1028 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1035 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1024))).fv) 0)

noncomputable def nb078_alpha_dummy_1036 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1027 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1037 : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1025))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) 0)

noncomputable def nb078_alpha_dummy_1038 (h : Var) : Var := (freshVar (((Class.cv (nb078_alpha_dummy_1028 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1028 h))).fv) 0)

noncomputable def nb078_alpha_dummy_1039 : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1009) (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1009)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1040 (h : Var) : Var := (freshVar (((Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1011 h) (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h)) (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb078_alpha_dummy_1041 : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_1042 (h : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb078_alpha_dummy_1043 : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv) 0)

noncomputable def nb078_alpha_dummy_1044 (h : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv) 0)

noncomputable def nb078_alpha_dummy_1045 : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_1046 (h : Var) : Var := (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv) 0)

noncomputable def nb078_alpha_dummy_1047 : Var := (freshVar (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002))) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_1048 (h : Var) : Var := (freshVar (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪ ((syn_cid)).fv) 0)

noncomputable def nb078_alpha_dummy_1049 : Var := (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
