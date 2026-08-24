import NominalAlphaCompactEnvFreshSupport002
import NominalAlphaTransport
import WPPCompactSourceSyntax
import WPPCompactSyntaxFVExplicit
import CoreFVSimp
import CompactSyntaxFVDisable
import ReplaySupport.Basic
import AlphaFocusedSupport
import FocusedFVPaths

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

noncomputable def nb097_alpha_dummy_000 (C : Class) (F : Class) : Var := (freshVar ((F).fv ∪ (C).fv) 0)

noncomputable def nb097_alpha_dummy_001 (C : Class) (F : Class) : Var := (freshVar ((F).fv ∪ (C).fv) 1)

noncomputable def nb097_alpha_dummy_002 (C : Class) (F : Class) : Var := (freshVar (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))).fv) 0)

noncomputable def nb097_alpha_dummy_003 (C : Class) (k : Var) (m : Var) (F : Class) : Var := (freshVar (({m} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv) 0)

noncomputable def nb097_alpha_dummy_004 (C : Class) (F : Class) : Var := (freshVar (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 0)

noncomputable def nb097_alpha_dummy_005 (C : Class) (F : Class) : Var := (freshVar (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 1)

noncomputable def nb097_alpha_dummy_006 (C : Class) (k : Var) (m : Var) (F : Class) : Var := (freshVar (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 0)

noncomputable def nb097_alpha_dummy_007 (C : Class) (k : Var) (m : Var) (F : Class) : Var := (freshVar (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 1)

noncomputable def nb097_alpha_dummy_008 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) 0)

noncomputable def nb097_alpha_dummy_009 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) 1)

noncomputable def nb097_alpha_dummy_010 (k : Var) (m : Var) : Var := (freshVar (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 0)

noncomputable def nb097_alpha_dummy_011 (k : Var) (m : Var) : Var := (freshVar (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 1)

noncomputable def nb097_alpha_dummy_012 (C : Class) (F : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb097_alpha_dummy_013 (k : Var) (m : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb097_alpha_dummy_014 (C : Class) (F : Class) : Var := (freshVar (((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv) 0)

noncomputable def nb097_alpha_dummy_015 (k : Var) (m : Var) : Var := (freshVar (((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv) 0)

noncomputable def nb097_alpha_dummy_016 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_009 C F))).fv) 0)

noncomputable def nb097_alpha_dummy_017 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_009 C F))).fv) 1)

noncomputable def nb097_alpha_dummy_018 (k : Var) (m : Var) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_011 k m))).fv) 0)

noncomputable def nb097_alpha_dummy_019 (k : Var) (m : Var) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_011 k m))).fv) 1)

noncomputable def nb097_alpha_dummy_020 (C : Class) (F : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb097_alpha_dummy_016 C F)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb097_alpha_dummy_016 C F)) (syn_c1c))).fv ∪ ((Class.cv (nb097_alpha_dummy_016 C F))).fv) 0)

noncomputable def nb097_alpha_dummy_021 (k : Var) (m : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb097_alpha_dummy_018 k m)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb097_alpha_dummy_018 k m)) (syn_c1c))).fv ∪ ((Class.cv (nb097_alpha_dummy_018 k m))).fv) 0)

noncomputable def nb097_alpha_dummy_022 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb097_alpha_dummy_023 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb097_alpha_dummy_024 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb097_alpha_dummy_025 (k : Var) (m : Var) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb097_alpha_dummy_026 (k : Var) (m : Var) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb097_alpha_dummy_027 (k : Var) (m : Var) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb097_alpha_dummy_028 (C : Class) (F : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv) 0)

noncomputable def nb097_alpha_dummy_029 (k : Var) (m : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv) 0)

noncomputable def nb097_alpha_dummy_030 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_024 C F))).fv) 0)

noncomputable def nb097_alpha_dummy_031 (k : Var) (m : Var) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_027 k m))).fv) 0)

noncomputable def nb097_alpha_dummy_032 (C : Class) (F : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv) 0)

noncomputable def nb097_alpha_dummy_033 (k : Var) (m : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv) 0)

noncomputable def nb097_alpha_dummy_034 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_023 C F))).fv) 0)

noncomputable def nb097_alpha_dummy_035 (k : Var) (m : Var) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_026 k m))).fv) 0)

noncomputable def nb097_alpha_dummy_036 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_024 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_024 C F))).fv) 0)

noncomputable def nb097_alpha_dummy_037 (k : Var) (m : Var) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_027 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_027 k m))).fv) 0)

noncomputable def nb097_alpha_dummy_038 (C : Class) (F : Class) : Var := (freshVar (((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb097_alpha_dummy_039 (k : Var) (m : Var) : Var := (freshVar (((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb097_alpha_dummy_040 (C : Class) (F : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb097_alpha_dummy_041 (k : Var) (m : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb097_alpha_dummy_042 (C : Class) (F : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv ∪ ((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv) 0)

noncomputable def nb097_alpha_dummy_043 (k : Var) (m : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv ∪ ((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv) 0)

noncomputable def nb097_alpha_dummy_044 (C : Class) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_002 C F))).fv) 0)

noncomputable def nb097_alpha_dummy_045 (C : Class) (k : Var) (m : Var) (F : Class) : Var := (freshVar (((Class.cv (nb097_alpha_dummy_003 C k m F))).fv) 0)

theorem nb097_fresh_000 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ∉ (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) := by
  simpa only [nb097_alpha_dummy_004] using freshVar_not_mem (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 0

theorem nb097_fresh_001 (C : Class) (F : Class) : (nb097_alpha_dummy_005 C F) ∉ (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) := by
  simpa only [nb097_alpha_dummy_005] using freshVar_not_mem (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 1

theorem nb097_distinct_002 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ≠ (nb097_alpha_dummy_005 C F) := by
  simpa only [nb097_alpha_dummy_004, nb097_alpha_dummy_005] using
    (freshVar_injective (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_003 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_006 C k m F) ∉ (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) := by
  simpa only [nb097_alpha_dummy_006] using freshVar_not_mem (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 0

theorem nb097_fresh_004 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_007 C k m F) ∉ (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) := by
  simpa only [nb097_alpha_dummy_007] using freshVar_not_mem (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 1

theorem nb097_distinct_005 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_006 C k m F) ≠ (nb097_alpha_dummy_007 C k m F) := by
  simpa only [nb097_alpha_dummy_006, nb097_alpha_dummy_007] using
    (freshVar_injective (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_006 (C : Class) (F : Class) : (nb097_alpha_dummy_038 C F) ∉ (((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb097_alpha_dummy_038] using freshVar_not_mem (((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb097_fresh_007 (C : Class) (F : Class) : (nb097_alpha_dummy_014 C F) ∉ (((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv) := by
  simpa only [nb097_alpha_dummy_014] using freshVar_not_mem (((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv) 0

theorem nb097_fresh_008 (k : Var) (m : Var) : (nb097_alpha_dummy_039 k m) ∉ (((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb097_alpha_dummy_039] using freshVar_not_mem (((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb097_fresh_009 (k : Var) (m : Var) : (nb097_alpha_dummy_015 k m) ∉ (((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv) := by
  simpa only [nb097_alpha_dummy_015] using freshVar_not_mem (((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv) 0

theorem nb097_fresh_010 (C : Class) (F : Class) : (nb097_alpha_dummy_008 C F) ∉ (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) := by
  simpa only [nb097_alpha_dummy_008] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) 0

theorem nb097_fresh_011 (C : Class) (F : Class) : (nb097_alpha_dummy_009 C F) ∉ (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) := by
  simpa only [nb097_alpha_dummy_009] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) 1

theorem nb097_distinct_012 (C : Class) (F : Class) : (nb097_alpha_dummy_008 C F) ≠ (nb097_alpha_dummy_009 C F) := by
  simpa only [nb097_alpha_dummy_008, nb097_alpha_dummy_009] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_013 (C : Class) (F : Class) : (nb097_alpha_dummy_044 C F) ∉ (((Class.cv (nb097_alpha_dummy_002 C F))).fv) := by
  simpa only [nb097_alpha_dummy_044] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_002 C F))).fv) 0

theorem nb097_fresh_014 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_045 C k m F) ∉ (((Class.cv (nb097_alpha_dummy_003 C k m F))).fv) := by
  simpa only [nb097_alpha_dummy_045] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_003 C k m F))).fv) 0

theorem nb097_fresh_015 (C : Class) (F : Class) : (nb097_alpha_dummy_016 C F) ∉ (((Class.cv (nb097_alpha_dummy_009 C F))).fv) := by
  simpa only [nb097_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_009 C F))).fv) 0

theorem nb097_fresh_016 (C : Class) (F : Class) : (nb097_alpha_dummy_017 C F) ∉ (((Class.cv (nb097_alpha_dummy_009 C F))).fv) := by
  simpa only [nb097_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_009 C F))).fv) 1

theorem nb097_distinct_017 (C : Class) (F : Class) : (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_017 C F) := by
  simpa only [nb097_alpha_dummy_016, nb097_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_009 C F))).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_018 (k : Var) (m : Var) : (nb097_alpha_dummy_018 k m) ∉ (((Class.cv (nb097_alpha_dummy_011 k m))).fv) := by
  simpa only [nb097_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_011 k m))).fv) 0

theorem nb097_fresh_019 (k : Var) (m : Var) : (nb097_alpha_dummy_019 k m) ∉ (((Class.cv (nb097_alpha_dummy_011 k m))).fv) := by
  simpa only [nb097_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_011 k m))).fv) 1

theorem nb097_distinct_020 (k : Var) (m : Var) : (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_019 k m) := by
  simpa only [nb097_alpha_dummy_018, nb097_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_011 k m))).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_021 (C : Class) (F : Class) : (nb097_alpha_dummy_022 C F) ∉ (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb097_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 0

theorem nb097_fresh_022 (C : Class) (F : Class) : (nb097_alpha_dummy_023 C F) ∉ (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb097_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 1

theorem nb097_fresh_023 (C : Class) (F : Class) : (nb097_alpha_dummy_024 C F) ∉ (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb097_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 2

theorem nb097_distinct_024 (C : Class) (F : Class) : (nb097_alpha_dummy_022 C F) ≠ (nb097_alpha_dummy_023 C F) := by
  simpa only [nb097_alpha_dummy_022, nb097_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb097_distinct_025 (C : Class) (F : Class) : (nb097_alpha_dummy_022 C F) ≠ (nb097_alpha_dummy_024 C F) := by
  simpa only [nb097_alpha_dummy_022, nb097_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb097_distinct_026 (C : Class) (F : Class) : (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_024 C F) := by
  simpa only [nb097_alpha_dummy_023, nb097_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb097_fresh_027 (k : Var) (m : Var) : (nb097_alpha_dummy_025 k m) ∉ (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb097_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 0

theorem nb097_fresh_028 (k : Var) (m : Var) : (nb097_alpha_dummy_026 k m) ∉ (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb097_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 1

theorem nb097_fresh_029 (k : Var) (m : Var) : (nb097_alpha_dummy_027 k m) ∉ (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb097_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 2

theorem nb097_distinct_030 (k : Var) (m : Var) : (nb097_alpha_dummy_025 k m) ≠ (nb097_alpha_dummy_026 k m) := by
  simpa only [nb097_alpha_dummy_025, nb097_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb097_distinct_031 (k : Var) (m : Var) : (nb097_alpha_dummy_025 k m) ≠ (nb097_alpha_dummy_027 k m) := by
  simpa only [nb097_alpha_dummy_025, nb097_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb097_distinct_032 (k : Var) (m : Var) : (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_027 k m) := by
  simpa only [nb097_alpha_dummy_026, nb097_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb097_fresh_033 (C : Class) (F : Class) : (nb097_alpha_dummy_034 C F) ∉ (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_023 C F))).fv) := by
  simpa only [nb097_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_023 C F))).fv) 0

theorem nb097_fresh_034 (C : Class) (F : Class) : (nb097_alpha_dummy_030 C F) ∉ (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_024 C F))).fv) := by
  simpa only [nb097_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_024 C F))).fv) 0

theorem nb097_fresh_035 (C : Class) (F : Class) : (nb097_alpha_dummy_036 C F) ∉ (((Class.cv (nb097_alpha_dummy_024 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_024 C F))).fv) := by
  simpa only [nb097_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_024 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_024 C F))).fv) 0

theorem nb097_fresh_036 (k : Var) (m : Var) : (nb097_alpha_dummy_035 k m) ∉ (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_026 k m))).fv) := by
  simpa only [nb097_alpha_dummy_035] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_026 k m))).fv) 0

theorem nb097_fresh_037 (k : Var) (m : Var) : (nb097_alpha_dummy_031 k m) ∉ (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_027 k m))).fv) := by
  simpa only [nb097_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_027 k m))).fv) 0

theorem nb097_fresh_038 (k : Var) (m : Var) : (nb097_alpha_dummy_037 k m) ∉ (((Class.cv (nb097_alpha_dummy_027 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_027 k m))).fv) := by
  simpa only [nb097_alpha_dummy_037] using freshVar_not_mem (((Class.cv (nb097_alpha_dummy_027 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_027 k m))).fv) 0

theorem nb097_fresh_039 (k : Var) (m : Var) : (nb097_alpha_dummy_010 k m) ∉ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) := by
  simpa only [nb097_alpha_dummy_010] using freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 0

theorem nb097_fresh_040 (k : Var) (m : Var) : (nb097_alpha_dummy_011 k m) ∉ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) := by
  simpa only [nb097_alpha_dummy_011] using freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 1

theorem nb097_distinct_041 (k : Var) (m : Var) : (nb097_alpha_dummy_010 k m) ≠ (nb097_alpha_dummy_011 k m) := by
  simpa only [nb097_alpha_dummy_010, nb097_alpha_dummy_011] using
    (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_042 (C : Class) (F : Class) : (nb097_alpha_dummy_020 C F) ∉ (((Wff.classMem (Class.cv (nb097_alpha_dummy_016 C F)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb097_alpha_dummy_016 C F)) (syn_c1c))).fv ∪ ((Class.cv (nb097_alpha_dummy_016 C F))).fv) := by
  simpa only [nb097_alpha_dummy_020] using freshVar_not_mem (((Wff.classMem (Class.cv (nb097_alpha_dummy_016 C F)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb097_alpha_dummy_016 C F)) (syn_c1c))).fv ∪ ((Class.cv (nb097_alpha_dummy_016 C F))).fv) 0

theorem nb097_fresh_043 (k : Var) (m : Var) : (nb097_alpha_dummy_021 k m) ∉ (((Wff.classMem (Class.cv (nb097_alpha_dummy_018 k m)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb097_alpha_dummy_018 k m)) (syn_c1c))).fv ∪ ((Class.cv (nb097_alpha_dummy_018 k m))).fv) := by
  simpa only [nb097_alpha_dummy_021] using freshVar_not_mem (((Wff.classMem (Class.cv (nb097_alpha_dummy_018 k m)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb097_alpha_dummy_018 k m)) (syn_c1c))).fv ∪ ((Class.cv (nb097_alpha_dummy_018 k m))).fv) 0

theorem nb097_fresh_044 (C : Class) (F : Class) : (nb097_alpha_dummy_012 C F) ∉ (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb097_alpha_dummy_012] using freshVar_not_mem (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb097_fresh_045 (k : Var) (m : Var) : (nb097_alpha_dummy_013 k m) ∉ (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb097_alpha_dummy_013] using freshVar_not_mem (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb097_fresh_046 (C : Class) (F : Class) : (nb097_alpha_dummy_032 C F) ∉ (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv) := by
  simpa only [nb097_alpha_dummy_032] using freshVar_not_mem (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv) 0

theorem nb097_fresh_047 (k : Var) (m : Var) : (nb097_alpha_dummy_033 k m) ∉ (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv) := by
  simpa only [nb097_alpha_dummy_033] using freshVar_not_mem (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv) 0

theorem nb097_fresh_048 (C : Class) (F : Class) : (nb097_alpha_dummy_040 C F) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb097_alpha_dummy_040] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb097_fresh_049 (k : Var) (m : Var) : (nb097_alpha_dummy_041 k m) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb097_alpha_dummy_041] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb097_fresh_050 (C : Class) (F : Class) : (nb097_alpha_dummy_028 C F) ∉ (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv) := by
  simpa only [nb097_alpha_dummy_028] using freshVar_not_mem (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv) 0

theorem nb097_fresh_051 (k : Var) (m : Var) : (nb097_alpha_dummy_029 k m) ∉ (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv) := by
  simpa only [nb097_alpha_dummy_029] using freshVar_not_mem (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv) 0

theorem nb097_fresh_052 (C : Class) (F : Class) : (nb097_alpha_dummy_042 C F) ∉ (((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv ∪ ((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv) := by
  simpa only [nb097_alpha_dummy_042] using freshVar_not_mem (((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv ∪ ((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv) 0

theorem nb097_fresh_053 (k : Var) (m : Var) : (nb097_alpha_dummy_043 k m) ∉ (((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv ∪ ((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv) := by
  simpa only [nb097_alpha_dummy_043] using freshVar_not_mem (((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv ∪ ((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv) 0

theorem nb097_fresh_054 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∉ ((F).fv ∪ (C).fv) := by
  simpa only [nb097_alpha_dummy_000] using freshVar_not_mem ((F).fv ∪ (C).fv) 0

theorem nb097_fresh_055 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∉ ((F).fv ∪ (C).fv) := by
  simpa only [nb097_alpha_dummy_001] using freshVar_not_mem ((F).fv ∪ (C).fv) 1

theorem nb097_distinct_056 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_001 C F) := by
  simpa only [nb097_alpha_dummy_000, nb097_alpha_dummy_001] using
    (freshVar_injective ((F).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_057 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∉ (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))).fv) := by
  simpa only [nb097_alpha_dummy_002] using freshVar_not_mem (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))).fv) 0

theorem nb097_fresh_058 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∉ (({m} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv) := by
  simpa only [nb097_alpha_dummy_003] using freshVar_not_mem (({m} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv) 0

theorem nb097_support_mem_0000 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∈ (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0001 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∈ (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0002 (k : Var) (m : Var) : m ∈ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0003 (k : Var) (m : Var) : m ∈ (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0004 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∈ (((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0005 (k : Var) (m : Var) : m ∈ (((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0006 (C : Class) (F : Class) : (nb097_alpha_dummy_009 C F) ∈ (((Class.cv (nb097_alpha_dummy_009 C F))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0007 (k : Var) (m : Var) : (nb097_alpha_dummy_011 k m) ∈ (((Class.cv (nb097_alpha_dummy_011 k m))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0008 (C : Class) (F : Class) : (nb097_alpha_dummy_016 C F) ∈ (((Wff.classMem (Class.cv (nb097_alpha_dummy_016 C F)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb097_alpha_dummy_016 C F)) (syn_c1c))).fv ∪ ((Class.cv (nb097_alpha_dummy_016 C F))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0009 (k : Var) (m : Var) : (nb097_alpha_dummy_018 k m) ∈ (((Wff.classMem (Class.cv (nb097_alpha_dummy_018 k m)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb097_alpha_dummy_018 k m)) (syn_c1c))).fv ∪ ((Class.cv (nb097_alpha_dummy_018 k m))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0010 (C : Class) (F : Class) : (nb097_alpha_dummy_016 C F) ∈ (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0011 (k : Var) (m : Var) : (nb097_alpha_dummy_018 k m) ∈ (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0012 (C : Class) (F : Class) : (nb097_alpha_dummy_023 C F) ∈ (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0013 (k : Var) (m : Var) : (nb097_alpha_dummy_026 k m) ∈ (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0014 (C : Class) (F : Class) : (nb097_alpha_dummy_023 C F) ∈ (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_024 C F))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0015 (k : Var) (m : Var) : (nb097_alpha_dummy_026 k m) ∈ (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_027 k m))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0016 (C : Class) (F : Class) : (nb097_alpha_dummy_024 C F) ∈ (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F)) (Class.cv (nb097_alpha_dummy_024 C F)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0017 (k : Var) (m : Var) : (nb097_alpha_dummy_027 k m) ∈ (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪ ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m)) (Class.cv (nb097_alpha_dummy_027 k m)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0018 (C : Class) (F : Class) : (nb097_alpha_dummy_024 C F) ∈ (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_024 C F))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0019 (k : Var) (m : Var) : (nb097_alpha_dummy_027 k m) ∈ (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_027 k m))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0020 (C : Class) (F : Class) : (nb097_alpha_dummy_023 C F) ∈ (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0021 (k : Var) (m : Var) : (nb097_alpha_dummy_026 k m) ∈ (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0022 (C : Class) (F : Class) : (nb097_alpha_dummy_023 C F) ∈ (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_023 C F))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0023 (k : Var) (m : Var) : (nb097_alpha_dummy_026 k m) ∈ (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_026 k m))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0024 (C : Class) (F : Class) : (nb097_alpha_dummy_024 C F) ∈ (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0025 (k : Var) (m : Var) : (nb097_alpha_dummy_027 k m) ∈ (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪ ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0026 (C : Class) (F : Class) : (nb097_alpha_dummy_024 C F) ∈ (((Class.cv (nb097_alpha_dummy_024 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_024 C F))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0027 (k : Var) (m : Var) : (nb097_alpha_dummy_027 k m) ∈ (((Class.cv (nb097_alpha_dummy_027 k m))).fv ∪ ((Class.cv (nb097_alpha_dummy_027 k m))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0028 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∈ (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0029 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∈ (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0030 (k : Var) (m : Var) : k ∈ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0031 (k : Var) (m : Var) : k ∈ (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0032 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∈ (((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F)) (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0033 (k : Var) (m : Var) : k ∈ (((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k) (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0034 (C : Class) (F : Class) : (nb097_alpha_dummy_009 C F) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0035 (k : Var) (m : Var) : (nb097_alpha_dummy_011 k m) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0036 (C : Class) (F : Class) : (nb097_alpha_dummy_009 C F) ∈ (((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv ∪ ((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0037 (k : Var) (m : Var) : (nb097_alpha_dummy_011 k m) ∈ (((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv ∪ ((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0038 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∈ (((Class.cv (nb097_alpha_dummy_002 C F))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0039 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∈ (((Class.cv (nb097_alpha_dummy_003 C k m F))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_focused_notmem_0000 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∉ C.fv := by
  change freshVar ((F).fv ∪ (C).fv) 1 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb097_focused_notmem_0001 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∉ F.fv := by
  change freshVar ((F).fv ∪ (C).fv) 1 ∉ F.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb097_wpp_notmem_0000 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_001, fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro (nb097_focused_notmem_0000 C F) (nb097_focused_notmem_0001 C F))

theorem nb097_wpp_notmem_0001 (C : Class) (m : Var) (F : Class) (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) : m ∉ ((syn_cwppcand F C)).fv := by
  simpa only [fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro dv_C_m dv_F_m)

theorem nb097_focused_notmem_0002 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∉ C.fv := by
  change freshVar (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_left _ (hu)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

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

theorem nb097_focused_notmem_0003 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∉ F.fv := by
  change freshVar (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))).fv) 0 ∉ F.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_right _ (hu)))))))))))

theorem nb097_wpp_notmem_0002 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_002, fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro (nb097_focused_notmem_0002 C F) (nb097_focused_notmem_0003 C F))

theorem nb097_focused_notmem_0004 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∉ C.fv := by
  change freshVar (({m} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv m) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_left _ (hu)))))))))))

theorem nb097_focused_notmem_0005 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∉ F.fv := by
  change freshVar (({m} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv) 0 ∉ F.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv m) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_right _ (hu)))))))))))

theorem nb097_wpp_notmem_0003 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_003, fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro (nb097_focused_notmem_0004 C k m F) (nb097_focused_notmem_0005 C k m F))

theorem nb097_focused_notmem_0006 (C : Class) (F : Class) : (nb097_alpha_dummy_005 C F) ∉ C.fv := by
  change freshVar (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 1 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => ((fv_class_cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0002 C F)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0000 C F)) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_left _ (hu))))))))))⟩))))))⟩)))

theorem nb097_focused_notmem_0007 (C : Class) (F : Class) : (nb097_alpha_dummy_005 C F) ∉ F.fv := by
  change freshVar (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 1 ∉ F.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => ((fv_class_cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0003 C F)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0001 C F)) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_right _ (hu))))))))))⟩))))))⟩)))

theorem nb097_wpp_notmem_0004 (C : Class) (F : Class) : (nb097_alpha_dummy_005 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_005, fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro (nb097_focused_notmem_0006 C F) (nb097_focused_notmem_0007 C F))

theorem nb097_focused_notmem_0008 (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_m : m ∉ C.fv) : (nb097_alpha_dummy_007 C k m F) ∉ C.fv := by
  change freshVar (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 1 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => ((fv_class_cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0004 C k m F)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_C_m) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv m) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_left _ (hu))))))))))⟩))))))⟩)))

theorem nb097_focused_notmem_0009 (C : Class) (k : Var) (m : Var) (F : Class) (dv_F_m : m ∉ F.fv) : (nb097_alpha_dummy_007 C k m F) ∉ F.fv := by
  change freshVar (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 1 ∉ F.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun _ hu => ((fv_class_cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0005 C k m F)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_F_m) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv m) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_right _ (hu))))))))))⟩))))))⟩)))

theorem nb097_wpp_notmem_0005 (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) : (nb097_alpha_dummy_007 C k m F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_007, fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro (nb097_focused_notmem_0008 C k m F dv_C_m) (nb097_focused_notmem_0009 C k m F dv_F_m))

theorem nb097_focused_notmem_0010 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ∉ C.fv := by
  change freshVar (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => ((fv_class_cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0002 C F)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0000 C F)) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_left _ (hu))))))))))⟩))))))⟩)))

theorem nb097_focused_notmem_0011 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ∉ F.fv := by
  change freshVar (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 0 ∉ F.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => ((fv_class_cab (nb097_alpha_dummy_002 C F) (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0003 C F)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))) (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab (nb097_alpha_dummy_001 C F) (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F)))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0001 C F)) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)) (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C) (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec) (Class.cv (nb097_alpha_dummy_000 C F))))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_right _ (hu))))))))))⟩))))))⟩)))

theorem nb097_wpp_notmem_0006 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_004, fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro (nb097_focused_notmem_0010 C F) (nb097_focused_notmem_0011 C F))

theorem nb097_focused_notmem_0012 (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_m : m ∉ C.fv) : (nb097_alpha_dummy_006 C k m F) ∉ C.fv := by
  change freshVar (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => ((fv_class_cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0004 C k m F)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_C_m) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv m) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_left _ (hu))))))))))⟩))))))⟩)))

theorem nb097_focused_notmem_0013 (C : Class) (k : Var) (m : Var) (F : Class) (dv_F_m : m ∉ F.fv) : (nb097_alpha_dummy_006 C k m F) ∉ F.fv := by
  change freshVar (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 0 ∉ F.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => ((fv_class_cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb097_focused_notmem_0005 C k m F)) (h_eq ▸ hu)), (((fv_wff_classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))) (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))).symm ▸ (Finset.mem_union_left _ (((fv_class_cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => (dv_F_m) (h_eq ▸ hu)), (((fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))).symm ▸ (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv m) (syn_cwppcand F C)).symm ▸ (Finset.mem_union_right _ (((fv_syn_cwppcand F C).symm ▸ (Finset.mem_union_right _ (hu))))))))))⟩))))))⟩)))

theorem nb097_wpp_notmem_0007 (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) : (nb097_alpha_dummy_006 C k m F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_006, fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro (nb097_focused_notmem_0012 C k m F dv_C_m) (nb097_focused_notmem_0013 C k m F dv_F_m))

theorem nb097_compact_envfresh_0000 (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) : TEnvFresh [((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_cwppcand F C)).fv := by
  exact (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0000 C F) (nb097_wpp_notmem_0001 C m F dv_C_m dv_F_m) (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F) (nb097_wpp_notmem_0002 C F) (nb097_wpp_notmem_0003 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F) (nb097_wpp_notmem_0004 C F) (nb097_wpp_notmem_0005 C k m F dv_C_m dv_F_m) (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0006 C F) (nb097_wpp_notmem_0007 C k m F dv_C_m dv_F_m) (TEnvFresh.nil ((syn_cwppcand F C)).fv)))))

noncomputable def nb097_wpp_refl_0000 (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) : TReflOn [((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_cwppcand F C)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0000 C k m F dv_C_m dv_F_m)

theorem nb097_focused_notmem_0014 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∉ C.fv := by
  change freshVar ((F).fv ∪ (C).fv) 0 ∉ C.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb097_focused_notmem_0015 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∉ F.fv := by
  change freshVar ((F).fv ∪ (C).fv) 0 ∉ F.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb097_wpp_notmem_0008 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_000, fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro (nb097_focused_notmem_0014 C F) (nb097_focused_notmem_0015 C F))

theorem nb097_wpp_notmem_0009 (C : Class) (k : Var) (F : Class) (dv_C_k : k ∉ C.fv) (dv_F_k : k ∉ F.fv) : k ∉ ((syn_cwppcand F C)).fv := by
  simpa only [fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro dv_C_k dv_F_k)

theorem nb097_compact_envfresh_0001 (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) : TEnvFresh [((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_cwppcand F C)).fv := by
  exact (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0008 C F) (nb097_wpp_notmem_0009 C k F dv_C_k dv_F_k) (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0000 C F) (nb097_wpp_notmem_0001 C m F dv_C_m dv_F_m) (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F) (nb097_wpp_notmem_0002 C F) (nb097_wpp_notmem_0003 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F) (nb097_wpp_notmem_0004 C F) (nb097_wpp_notmem_0005 C k m F dv_C_m dv_F_m) (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0006 C F) (nb097_wpp_notmem_0007 C k m F dv_C_m dv_F_m) (TEnvFresh.nil ((syn_cwppcand F C)).fv))))))

noncomputable def nb097_wpp_refl_0001 (C : Class) (k : Var) (m : Var) (F : Class) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) : TReflOn [((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_cwppcand F C)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0001 C k m F dv_C_k dv_C_m dv_F_k dv_F_m)

theorem nb097_compact_fv_empty_0000 (C : Class) (F : Class) : (nb097_alpha_dummy_024 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0010 (C : Class) (F : Class) : (nb097_alpha_dummy_024 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_024, fv_syn_c1c] using (nb097_compact_fv_empty_0000 C F)

theorem nb097_compact_fv_empty_0001 (k : Var) (m : Var) : (nb097_alpha_dummy_027 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0011 (k : Var) (m : Var) : (nb097_alpha_dummy_027 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_027, fv_syn_c1c] using (nb097_compact_fv_empty_0001 k m)

theorem nb097_compact_fv_empty_0002 (C : Class) (F : Class) : (nb097_alpha_dummy_023 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0012 (C : Class) (F : Class) : (nb097_alpha_dummy_023 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_023, fv_syn_c1c] using (nb097_compact_fv_empty_0002 C F)

theorem nb097_compact_fv_empty_0003 (k : Var) (m : Var) : (nb097_alpha_dummy_026 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0013 (k : Var) (m : Var) : (nb097_alpha_dummy_026 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_026, fv_syn_c1c] using (nb097_compact_fv_empty_0003 k m)

theorem nb097_compact_fv_empty_0004 (C : Class) (F : Class) : (nb097_alpha_dummy_022 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0014 (C : Class) (F : Class) : (nb097_alpha_dummy_022 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_022, fv_syn_c1c] using (nb097_compact_fv_empty_0004 C F)

theorem nb097_compact_fv_empty_0005 (k : Var) (m : Var) : (nb097_alpha_dummy_025 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0015 (k : Var) (m : Var) : (nb097_alpha_dummy_025 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_025, fv_syn_c1c] using (nb097_compact_fv_empty_0005 k m)

theorem nb097_compact_fv_empty_0006 (C : Class) (F : Class) : (nb097_alpha_dummy_020 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0016 (C : Class) (F : Class) : (nb097_alpha_dummy_020 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_020, fv_syn_c1c] using (nb097_compact_fv_empty_0006 C F)

theorem nb097_compact_fv_empty_0007 (k : Var) (m : Var) : (nb097_alpha_dummy_021 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0017 (k : Var) (m : Var) : (nb097_alpha_dummy_021 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_021, fv_syn_c1c] using (nb097_compact_fv_empty_0007 k m)

theorem nb097_compact_fv_empty_0008 (C : Class) (F : Class) : (nb097_alpha_dummy_016 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0018 (C : Class) (F : Class) : (nb097_alpha_dummy_016 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_016, fv_syn_c1c] using (nb097_compact_fv_empty_0008 C F)

theorem nb097_compact_fv_empty_0009 (k : Var) (m : Var) : (nb097_alpha_dummy_018 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0019 (k : Var) (m : Var) : (nb097_alpha_dummy_018 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_018, fv_syn_c1c] using (nb097_compact_fv_empty_0009 k m)

theorem nb097_compact_fv_empty_0010 (C : Class) (F : Class) : (nb097_alpha_dummy_017 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0020 (C : Class) (F : Class) : (nb097_alpha_dummy_017 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_017, fv_syn_c1c] using (nb097_compact_fv_empty_0010 C F)

theorem nb097_compact_fv_empty_0011 (k : Var) (m : Var) : (nb097_alpha_dummy_019 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0021 (k : Var) (m : Var) : (nb097_alpha_dummy_019 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_019, fv_syn_c1c] using (nb097_compact_fv_empty_0011 k m)

theorem nb097_compact_fv_empty_0012 (C : Class) (F : Class) : (nb097_alpha_dummy_009 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0022 (C : Class) (F : Class) : (nb097_alpha_dummy_009 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_009, fv_syn_c1c] using (nb097_compact_fv_empty_0012 C F)

theorem nb097_compact_fv_empty_0013 (k : Var) (m : Var) : (nb097_alpha_dummy_011 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0023 (k : Var) (m : Var) : (nb097_alpha_dummy_011 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_011, fv_syn_c1c] using (nb097_compact_fv_empty_0013 k m)

theorem nb097_compact_fv_empty_0014 (C : Class) (F : Class) : (nb097_alpha_dummy_008 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0024 (C : Class) (F : Class) : (nb097_alpha_dummy_008 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_008, fv_syn_c1c] using (nb097_compact_fv_empty_0014 C F)

theorem nb097_compact_fv_empty_0015 (k : Var) (m : Var) : (nb097_alpha_dummy_010 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0025 (k : Var) (m : Var) : (nb097_alpha_dummy_010 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_010, fv_syn_c1c] using (nb097_compact_fv_empty_0015 k m)

theorem nb097_compact_fv_empty_0016 (C : Class) (F : Class) : (nb097_alpha_dummy_014 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0026 (C : Class) (F : Class) : (nb097_alpha_dummy_014 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_014, fv_syn_c1c] using (nb097_compact_fv_empty_0016 C F)

theorem nb097_compact_fv_empty_0017 (k : Var) (m : Var) : (nb097_alpha_dummy_015 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0027 (k : Var) (m : Var) : (nb097_alpha_dummy_015 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_015, fv_syn_c1c] using (nb097_compact_fv_empty_0017 k m)

theorem nb097_compact_fv_empty_0018 (C : Class) (F : Class) : (nb097_alpha_dummy_012 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0028 (C : Class) (F : Class) : (nb097_alpha_dummy_012 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_012, fv_syn_c1c] using (nb097_compact_fv_empty_0018 C F)

theorem nb097_compact_fv_empty_0019 (k : Var) (m : Var) : (nb097_alpha_dummy_013 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0029 (k : Var) (m : Var) : (nb097_alpha_dummy_013 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_013, fv_syn_c1c] using (nb097_compact_fv_empty_0019 k m)

theorem nb097_compact_fv_empty_0020 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0030 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_000, fv_syn_c1c] using (nb097_compact_fv_empty_0020 C F)

theorem nb097_compact_fv_empty_0021 (k : Var) : k ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0031 (k : Var) : k ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb097_compact_fv_empty_0021 k)

theorem nb097_compact_fv_empty_0022 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0032 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_001, fv_syn_c1c] using (nb097_compact_fv_empty_0022 C F)

theorem nb097_compact_fv_empty_0023 (m : Var) : m ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0033 (m : Var) : m ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb097_compact_fv_empty_0023 m)

theorem nb097_compact_fv_empty_0024 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0034 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_002, fv_syn_c1c] using (nb097_compact_fv_empty_0024 C F)

theorem nb097_compact_fv_empty_0025 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0035 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_003, fv_syn_c1c] using (nb097_compact_fv_empty_0025 C k m F)

theorem nb097_compact_fv_empty_0026 (C : Class) (F : Class) : (nb097_alpha_dummy_005 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0036 (C : Class) (F : Class) : (nb097_alpha_dummy_005 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_005, fv_syn_c1c] using (nb097_compact_fv_empty_0026 C F)

theorem nb097_compact_fv_empty_0027 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_007 C k m F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0037 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_007 C k m F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_007, fv_syn_c1c] using (nb097_compact_fv_empty_0027 C k m F)

theorem nb097_compact_fv_empty_0028 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0038 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_004, fv_syn_c1c] using (nb097_compact_fv_empty_0028 C F)

theorem nb097_compact_fv_empty_0029 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_006 C k m F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0039 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_006 C k m F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_006, fv_syn_c1c] using (nb097_compact_fv_empty_0029 C k m F)

theorem nb097_compact_envfresh_0002 (C : Class) (k : Var) (m : Var) (F : Class) : TEnvFresh [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb097_alpha_dummy_024 C F) (nb097_alpha_dummy_027 k m) (nb097_wpp_notmem_0010 C F) (nb097_wpp_notmem_0011 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_023 C F) (nb097_alpha_dummy_026 k m) (nb097_wpp_notmem_0012 C F) (nb097_wpp_notmem_0013 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_022 C F) (nb097_alpha_dummy_025 k m) (nb097_wpp_notmem_0014 C F) (nb097_wpp_notmem_0015 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_020 C F) (nb097_alpha_dummy_021 k m) (nb097_wpp_notmem_0016 C F) (nb097_wpp_notmem_0017 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_016 C F) (nb097_alpha_dummy_018 k m) (nb097_wpp_notmem_0018 C F) (nb097_wpp_notmem_0019 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_017 C F) (nb097_alpha_dummy_019 k m) (nb097_wpp_notmem_0020 C F) (nb097_wpp_notmem_0021 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_009 C F) (nb097_alpha_dummy_011 k m) (nb097_wpp_notmem_0022 C F) (nb097_wpp_notmem_0023 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_008 C F) (nb097_alpha_dummy_010 k m) (nb097_wpp_notmem_0024 C F) (nb097_wpp_notmem_0025 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_014 C F) (nb097_alpha_dummy_015 k m) (nb097_wpp_notmem_0026 C F) (nb097_wpp_notmem_0027 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_012 C F) (nb097_alpha_dummy_013 k m) (nb097_wpp_notmem_0028 C F) (nb097_wpp_notmem_0029 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0030 C F) (nb097_wpp_notmem_0031 k) (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0032 C F) (nb097_wpp_notmem_0033 m) (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F) (nb097_wpp_notmem_0034 C F) (nb097_wpp_notmem_0035 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F) (nb097_wpp_notmem_0036 C F) (nb097_wpp_notmem_0037 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0038 C F) (nb097_wpp_notmem_0039 C k m F) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb097_wpp_refl_0002 (C : Class) (k : Var) (m : Var) (F : Class) : TReflOn [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0002 C k m F)

theorem nb097_wpp_notmem_0040 (C : Class) (F : Class) : (nb097_alpha_dummy_024 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_024, fv_syn_c0] using (nb097_compact_fv_empty_0000 C F)

theorem nb097_wpp_notmem_0041 (k : Var) (m : Var) : (nb097_alpha_dummy_027 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_027, fv_syn_c0] using (nb097_compact_fv_empty_0001 k m)

theorem nb097_wpp_notmem_0042 (C : Class) (F : Class) : (nb097_alpha_dummy_023 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_023, fv_syn_c0] using (nb097_compact_fv_empty_0002 C F)

theorem nb097_wpp_notmem_0043 (k : Var) (m : Var) : (nb097_alpha_dummy_026 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_026, fv_syn_c0] using (nb097_compact_fv_empty_0003 k m)

theorem nb097_wpp_notmem_0044 (C : Class) (F : Class) : (nb097_alpha_dummy_022 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_022, fv_syn_c0] using (nb097_compact_fv_empty_0004 C F)

theorem nb097_wpp_notmem_0045 (k : Var) (m : Var) : (nb097_alpha_dummy_025 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_025, fv_syn_c0] using (nb097_compact_fv_empty_0005 k m)

theorem nb097_wpp_notmem_0046 (C : Class) (F : Class) : (nb097_alpha_dummy_020 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_020, fv_syn_c0] using (nb097_compact_fv_empty_0006 C F)

theorem nb097_wpp_notmem_0047 (k : Var) (m : Var) : (nb097_alpha_dummy_021 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_021, fv_syn_c0] using (nb097_compact_fv_empty_0007 k m)

theorem nb097_wpp_notmem_0048 (C : Class) (F : Class) : (nb097_alpha_dummy_016 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_016, fv_syn_c0] using (nb097_compact_fv_empty_0008 C F)

theorem nb097_wpp_notmem_0049 (k : Var) (m : Var) : (nb097_alpha_dummy_018 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_018, fv_syn_c0] using (nb097_compact_fv_empty_0009 k m)

theorem nb097_wpp_notmem_0050 (C : Class) (F : Class) : (nb097_alpha_dummy_017 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_017, fv_syn_c0] using (nb097_compact_fv_empty_0010 C F)

theorem nb097_wpp_notmem_0051 (k : Var) (m : Var) : (nb097_alpha_dummy_019 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_019, fv_syn_c0] using (nb097_compact_fv_empty_0011 k m)

theorem nb097_wpp_notmem_0052 (C : Class) (F : Class) : (nb097_alpha_dummy_009 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_009, fv_syn_c0] using (nb097_compact_fv_empty_0012 C F)

theorem nb097_wpp_notmem_0053 (k : Var) (m : Var) : (nb097_alpha_dummy_011 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_011, fv_syn_c0] using (nb097_compact_fv_empty_0013 k m)

theorem nb097_wpp_notmem_0054 (C : Class) (F : Class) : (nb097_alpha_dummy_008 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_008, fv_syn_c0] using (nb097_compact_fv_empty_0014 C F)

theorem nb097_wpp_notmem_0055 (k : Var) (m : Var) : (nb097_alpha_dummy_010 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_010, fv_syn_c0] using (nb097_compact_fv_empty_0015 k m)

theorem nb097_wpp_notmem_0056 (C : Class) (F : Class) : (nb097_alpha_dummy_014 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_014, fv_syn_c0] using (nb097_compact_fv_empty_0016 C F)

theorem nb097_wpp_notmem_0057 (k : Var) (m : Var) : (nb097_alpha_dummy_015 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_015, fv_syn_c0] using (nb097_compact_fv_empty_0017 k m)

theorem nb097_wpp_notmem_0058 (C : Class) (F : Class) : (nb097_alpha_dummy_012 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_012, fv_syn_c0] using (nb097_compact_fv_empty_0018 C F)

theorem nb097_wpp_notmem_0059 (k : Var) (m : Var) : (nb097_alpha_dummy_013 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_013, fv_syn_c0] using (nb097_compact_fv_empty_0019 k m)

theorem nb097_wpp_notmem_0060 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_000, fv_syn_c0] using (nb097_compact_fv_empty_0020 C F)

theorem nb097_wpp_notmem_0061 (k : Var) : k ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb097_compact_fv_empty_0021 k)

theorem nb097_wpp_notmem_0062 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_001, fv_syn_c0] using (nb097_compact_fv_empty_0022 C F)

theorem nb097_wpp_notmem_0063 (m : Var) : m ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb097_compact_fv_empty_0023 m)

theorem nb097_wpp_notmem_0064 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_002, fv_syn_c0] using (nb097_compact_fv_empty_0024 C F)

theorem nb097_wpp_notmem_0065 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_003, fv_syn_c0] using (nb097_compact_fv_empty_0025 C k m F)

theorem nb097_wpp_notmem_0066 (C : Class) (F : Class) : (nb097_alpha_dummy_005 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_005, fv_syn_c0] using (nb097_compact_fv_empty_0026 C F)

theorem nb097_wpp_notmem_0067 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_007 C k m F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_007, fv_syn_c0] using (nb097_compact_fv_empty_0027 C k m F)

theorem nb097_wpp_notmem_0068 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_004, fv_syn_c0] using (nb097_compact_fv_empty_0028 C F)

theorem nb097_wpp_notmem_0069 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_006 C k m F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_006, fv_syn_c0] using (nb097_compact_fv_empty_0029 C k m F)

theorem nb097_compact_envfresh_0003 (C : Class) (k : Var) (m : Var) (F : Class) : TEnvFresh [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb097_alpha_dummy_024 C F) (nb097_alpha_dummy_027 k m) (nb097_wpp_notmem_0040 C F) (nb097_wpp_notmem_0041 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_023 C F) (nb097_alpha_dummy_026 k m) (nb097_wpp_notmem_0042 C F) (nb097_wpp_notmem_0043 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_022 C F) (nb097_alpha_dummy_025 k m) (nb097_wpp_notmem_0044 C F) (nb097_wpp_notmem_0045 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_020 C F) (nb097_alpha_dummy_021 k m) (nb097_wpp_notmem_0046 C F) (nb097_wpp_notmem_0047 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_016 C F) (nb097_alpha_dummy_018 k m) (nb097_wpp_notmem_0048 C F) (nb097_wpp_notmem_0049 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_017 C F) (nb097_alpha_dummy_019 k m) (nb097_wpp_notmem_0050 C F) (nb097_wpp_notmem_0051 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_009 C F) (nb097_alpha_dummy_011 k m) (nb097_wpp_notmem_0052 C F) (nb097_wpp_notmem_0053 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_008 C F) (nb097_alpha_dummy_010 k m) (nb097_wpp_notmem_0054 C F) (nb097_wpp_notmem_0055 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_014 C F) (nb097_alpha_dummy_015 k m) (nb097_wpp_notmem_0056 C F) (nb097_wpp_notmem_0057 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_012 C F) (nb097_alpha_dummy_013 k m) (nb097_wpp_notmem_0058 C F) (nb097_wpp_notmem_0059 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0060 C F) (nb097_wpp_notmem_0061 k) (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0062 C F) (nb097_wpp_notmem_0063 m) (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F) (nb097_wpp_notmem_0064 C F) (nb097_wpp_notmem_0065 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F) (nb097_wpp_notmem_0066 C F) (nb097_wpp_notmem_0067 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0068 C F) (nb097_wpp_notmem_0069 C k m F) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb097_wpp_refl_0003 (C : Class) (k : Var) (m : Var) (F : Class) : TReflOn [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0003 C k m F)

theorem nb097_wpp_notmem_0070 (C : Class) (F : Class) : (nb097_alpha_dummy_020 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_020, fv_syn_cnnc] using (nb097_compact_fv_empty_0006 C F)

theorem nb097_wpp_notmem_0071 (k : Var) (m : Var) : (nb097_alpha_dummy_021 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_021, fv_syn_cnnc] using (nb097_compact_fv_empty_0007 k m)

theorem nb097_wpp_notmem_0072 (C : Class) (F : Class) : (nb097_alpha_dummy_016 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_016, fv_syn_cnnc] using (nb097_compact_fv_empty_0008 C F)

theorem nb097_wpp_notmem_0073 (k : Var) (m : Var) : (nb097_alpha_dummy_018 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_018, fv_syn_cnnc] using (nb097_compact_fv_empty_0009 k m)

theorem nb097_wpp_notmem_0074 (C : Class) (F : Class) : (nb097_alpha_dummy_017 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_017, fv_syn_cnnc] using (nb097_compact_fv_empty_0010 C F)

theorem nb097_wpp_notmem_0075 (k : Var) (m : Var) : (nb097_alpha_dummy_019 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_019, fv_syn_cnnc] using (nb097_compact_fv_empty_0011 k m)

theorem nb097_wpp_notmem_0076 (C : Class) (F : Class) : (nb097_alpha_dummy_009 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_009, fv_syn_cnnc] using (nb097_compact_fv_empty_0012 C F)

theorem nb097_wpp_notmem_0077 (k : Var) (m : Var) : (nb097_alpha_dummy_011 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_011, fv_syn_cnnc] using (nb097_compact_fv_empty_0013 k m)

theorem nb097_wpp_notmem_0078 (C : Class) (F : Class) : (nb097_alpha_dummy_008 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_008, fv_syn_cnnc] using (nb097_compact_fv_empty_0014 C F)

theorem nb097_wpp_notmem_0079 (k : Var) (m : Var) : (nb097_alpha_dummy_010 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_010, fv_syn_cnnc] using (nb097_compact_fv_empty_0015 k m)

theorem nb097_wpp_notmem_0080 (C : Class) (F : Class) : (nb097_alpha_dummy_014 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_014, fv_syn_cnnc] using (nb097_compact_fv_empty_0016 C F)

theorem nb097_wpp_notmem_0081 (k : Var) (m : Var) : (nb097_alpha_dummy_015 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_015, fv_syn_cnnc] using (nb097_compact_fv_empty_0017 k m)

theorem nb097_wpp_notmem_0082 (C : Class) (F : Class) : (nb097_alpha_dummy_012 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_012, fv_syn_cnnc] using (nb097_compact_fv_empty_0018 C F)

theorem nb097_wpp_notmem_0083 (k : Var) (m : Var) : (nb097_alpha_dummy_013 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_013, fv_syn_cnnc] using (nb097_compact_fv_empty_0019 k m)

theorem nb097_wpp_notmem_0084 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_000, fv_syn_cnnc] using (nb097_compact_fv_empty_0020 C F)

theorem nb097_wpp_notmem_0085 (k : Var) : k ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb097_compact_fv_empty_0021 k)

theorem nb097_wpp_notmem_0086 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_001, fv_syn_cnnc] using (nb097_compact_fv_empty_0022 C F)

theorem nb097_wpp_notmem_0087 (m : Var) : m ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb097_compact_fv_empty_0023 m)

theorem nb097_wpp_notmem_0088 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_002, fv_syn_cnnc] using (nb097_compact_fv_empty_0024 C F)

theorem nb097_wpp_notmem_0089 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_003, fv_syn_cnnc] using (nb097_compact_fv_empty_0025 C k m F)

theorem nb097_wpp_notmem_0090 (C : Class) (F : Class) : (nb097_alpha_dummy_005 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_005, fv_syn_cnnc] using (nb097_compact_fv_empty_0026 C F)

theorem nb097_wpp_notmem_0091 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_007 C k m F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_007, fv_syn_cnnc] using (nb097_compact_fv_empty_0027 C k m F)

theorem nb097_wpp_notmem_0092 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_004, fv_syn_cnnc] using (nb097_compact_fv_empty_0028 C F)

theorem nb097_wpp_notmem_0093 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_006 C k m F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_006, fv_syn_cnnc] using (nb097_compact_fv_empty_0029 C k m F)

theorem nb097_compact_envfresh_0004 (C : Class) (k : Var) (m : Var) (F : Class) : TEnvFresh [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb097_alpha_dummy_020 C F) (nb097_alpha_dummy_021 k m) (nb097_wpp_notmem_0070 C F) (nb097_wpp_notmem_0071 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_016 C F) (nb097_alpha_dummy_018 k m) (nb097_wpp_notmem_0072 C F) (nb097_wpp_notmem_0073 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_017 C F) (nb097_alpha_dummy_019 k m) (nb097_wpp_notmem_0074 C F) (nb097_wpp_notmem_0075 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_009 C F) (nb097_alpha_dummy_011 k m) (nb097_wpp_notmem_0076 C F) (nb097_wpp_notmem_0077 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_008 C F) (nb097_alpha_dummy_010 k m) (nb097_wpp_notmem_0078 C F) (nb097_wpp_notmem_0079 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_014 C F) (nb097_alpha_dummy_015 k m) (nb097_wpp_notmem_0080 C F) (nb097_wpp_notmem_0081 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_012 C F) (nb097_alpha_dummy_013 k m) (nb097_wpp_notmem_0082 C F) (nb097_wpp_notmem_0083 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0084 C F) (nb097_wpp_notmem_0085 k) (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0086 C F) (nb097_wpp_notmem_0087 m) (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F) (nb097_wpp_notmem_0088 C F) (nb097_wpp_notmem_0089 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F) (nb097_wpp_notmem_0090 C F) (nb097_wpp_notmem_0091 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0092 C F) (nb097_wpp_notmem_0093 C k m F) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb097_wpp_refl_0004 (C : Class) (k : Var) (m : Var) (F : Class) : TReflOn [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0004 C k m F)

theorem nb097_compact_fv_empty_0030 (C : Class) (F : Class) : (nb097_alpha_dummy_042 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0094 (C : Class) (F : Class) : (nb097_alpha_dummy_042 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_042, fv_syn_c1c] using (nb097_compact_fv_empty_0030 C F)

theorem nb097_compact_fv_empty_0031 (k : Var) (m : Var) : (nb097_alpha_dummy_043 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0095 (k : Var) (m : Var) : (nb097_alpha_dummy_043 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_043, fv_syn_c1c] using (nb097_compact_fv_empty_0031 k m)

theorem nb097_compact_fv_empty_0032 (C : Class) (F : Class) : (nb097_alpha_dummy_040 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

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

theorem nb097_wpp_notmem_0096 (C : Class) (F : Class) : (nb097_alpha_dummy_040 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_040, fv_syn_c1c] using (nb097_compact_fv_empty_0032 C F)

theorem nb097_compact_fv_empty_0033 (k : Var) (m : Var) : (nb097_alpha_dummy_041 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0097 (k : Var) (m : Var) : (nb097_alpha_dummy_041 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_041, fv_syn_c1c] using (nb097_compact_fv_empty_0033 k m)

theorem nb097_compact_fv_empty_0034 (C : Class) (F : Class) : (nb097_alpha_dummy_038 C F) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0098 (C : Class) (F : Class) : (nb097_alpha_dummy_038 C F) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_038, fv_syn_c1c] using (nb097_compact_fv_empty_0034 C F)

theorem nb097_compact_fv_empty_0035 (k : Var) (m : Var) : (nb097_alpha_dummy_039 k m) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb097_wpp_notmem_0099 (k : Var) (m : Var) : (nb097_alpha_dummy_039 k m) ∉ ((syn_c1c)).fv := by
  simpa only [nb097_alpha_dummy_039, fv_syn_c1c] using (nb097_compact_fv_empty_0035 k m)

theorem nb097_compact_envfresh_0005 (C : Class) (k : Var) (m : Var) (F : Class) : TEnvFresh [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb097_alpha_dummy_024 C F) (nb097_alpha_dummy_027 k m) (nb097_wpp_notmem_0010 C F) (nb097_wpp_notmem_0011 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_023 C F) (nb097_alpha_dummy_026 k m) (nb097_wpp_notmem_0012 C F) (nb097_wpp_notmem_0013 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_022 C F) (nb097_alpha_dummy_025 k m) (nb097_wpp_notmem_0014 C F) (nb097_wpp_notmem_0015 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_020 C F) (nb097_alpha_dummy_021 k m) (nb097_wpp_notmem_0016 C F) (nb097_wpp_notmem_0017 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_016 C F) (nb097_alpha_dummy_018 k m) (nb097_wpp_notmem_0018 C F) (nb097_wpp_notmem_0019 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_017 C F) (nb097_alpha_dummy_019 k m) (nb097_wpp_notmem_0020 C F) (nb097_wpp_notmem_0021 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_042 C F) (nb097_alpha_dummy_043 k m) (nb097_wpp_notmem_0094 C F) (nb097_wpp_notmem_0095 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_040 C F) (nb097_alpha_dummy_041 k m) (nb097_wpp_notmem_0096 C F) (nb097_wpp_notmem_0097 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_009 C F) (nb097_alpha_dummy_011 k m) (nb097_wpp_notmem_0022 C F) (nb097_wpp_notmem_0023 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_008 C F) (nb097_alpha_dummy_010 k m) (nb097_wpp_notmem_0024 C F) (nb097_wpp_notmem_0025 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_038 C F) (nb097_alpha_dummy_039 k m) (nb097_wpp_notmem_0098 C F) (nb097_wpp_notmem_0099 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_012 C F) (nb097_alpha_dummy_013 k m) (nb097_wpp_notmem_0028 C F) (nb097_wpp_notmem_0029 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0030 C F) (nb097_wpp_notmem_0031 k) (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0032 C F) (nb097_wpp_notmem_0033 m) (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F) (nb097_wpp_notmem_0034 C F) (nb097_wpp_notmem_0035 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F) (nb097_wpp_notmem_0036 C F) (nb097_wpp_notmem_0037 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0038 C F) (nb097_wpp_notmem_0039 C k m F) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb097_wpp_refl_0005 (C : Class) (k : Var) (m : Var) (F : Class) : TReflOn [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0005 C k m F)

theorem nb097_wpp_notmem_0100 (C : Class) (F : Class) : (nb097_alpha_dummy_042 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_042, fv_syn_c0] using (nb097_compact_fv_empty_0030 C F)

theorem nb097_wpp_notmem_0101 (k : Var) (m : Var) : (nb097_alpha_dummy_043 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_043, fv_syn_c0] using (nb097_compact_fv_empty_0031 k m)

theorem nb097_wpp_notmem_0102 (C : Class) (F : Class) : (nb097_alpha_dummy_040 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_040, fv_syn_c0] using (nb097_compact_fv_empty_0032 C F)

theorem nb097_wpp_notmem_0103 (k : Var) (m : Var) : (nb097_alpha_dummy_041 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_041, fv_syn_c0] using (nb097_compact_fv_empty_0033 k m)

theorem nb097_wpp_notmem_0104 (C : Class) (F : Class) : (nb097_alpha_dummy_038 C F) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_038, fv_syn_c0] using (nb097_compact_fv_empty_0034 C F)

theorem nb097_wpp_notmem_0105 (k : Var) (m : Var) : (nb097_alpha_dummy_039 k m) ∉ ((syn_c0)).fv := by
  simpa only [nb097_alpha_dummy_039, fv_syn_c0] using (nb097_compact_fv_empty_0035 k m)

theorem nb097_compact_envfresh_0006 (C : Class) (k : Var) (m : Var) (F : Class) : TEnvFresh [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb097_alpha_dummy_024 C F) (nb097_alpha_dummy_027 k m) (nb097_wpp_notmem_0040 C F) (nb097_wpp_notmem_0041 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_023 C F) (nb097_alpha_dummy_026 k m) (nb097_wpp_notmem_0042 C F) (nb097_wpp_notmem_0043 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_022 C F) (nb097_alpha_dummy_025 k m) (nb097_wpp_notmem_0044 C F) (nb097_wpp_notmem_0045 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_020 C F) (nb097_alpha_dummy_021 k m) (nb097_wpp_notmem_0046 C F) (nb097_wpp_notmem_0047 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_016 C F) (nb097_alpha_dummy_018 k m) (nb097_wpp_notmem_0048 C F) (nb097_wpp_notmem_0049 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_017 C F) (nb097_alpha_dummy_019 k m) (nb097_wpp_notmem_0050 C F) (nb097_wpp_notmem_0051 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_042 C F) (nb097_alpha_dummy_043 k m) (nb097_wpp_notmem_0100 C F) (nb097_wpp_notmem_0101 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_040 C F) (nb097_alpha_dummy_041 k m) (nb097_wpp_notmem_0102 C F) (nb097_wpp_notmem_0103 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_009 C F) (nb097_alpha_dummy_011 k m) (nb097_wpp_notmem_0052 C F) (nb097_wpp_notmem_0053 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_008 C F) (nb097_alpha_dummy_010 k m) (nb097_wpp_notmem_0054 C F) (nb097_wpp_notmem_0055 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_038 C F) (nb097_alpha_dummy_039 k m) (nb097_wpp_notmem_0104 C F) (nb097_wpp_notmem_0105 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_012 C F) (nb097_alpha_dummy_013 k m) (nb097_wpp_notmem_0058 C F) (nb097_wpp_notmem_0059 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0060 C F) (nb097_wpp_notmem_0061 k) (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0062 C F) (nb097_wpp_notmem_0063 m) (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F) (nb097_wpp_notmem_0064 C F) (nb097_wpp_notmem_0065 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F) (nb097_wpp_notmem_0066 C F) (nb097_wpp_notmem_0067 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0068 C F) (nb097_wpp_notmem_0069 C k m F) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb097_wpp_refl_0006 (C : Class) (k : Var) (m : Var) (F : Class) : TReflOn [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0006 C k m F)

theorem nb097_wpp_notmem_0106 (C : Class) (F : Class) : (nb097_alpha_dummy_042 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_042, fv_syn_cnnc] using (nb097_compact_fv_empty_0030 C F)

theorem nb097_wpp_notmem_0107 (k : Var) (m : Var) : (nb097_alpha_dummy_043 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_043, fv_syn_cnnc] using (nb097_compact_fv_empty_0031 k m)

theorem nb097_wpp_notmem_0108 (C : Class) (F : Class) : (nb097_alpha_dummy_040 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_040, fv_syn_cnnc] using (nb097_compact_fv_empty_0032 C F)

theorem nb097_wpp_notmem_0109 (k : Var) (m : Var) : (nb097_alpha_dummy_041 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_041, fv_syn_cnnc] using (nb097_compact_fv_empty_0033 k m)

theorem nb097_wpp_notmem_0110 (C : Class) (F : Class) : (nb097_alpha_dummy_038 C F) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_038, fv_syn_cnnc] using (nb097_compact_fv_empty_0034 C F)

theorem nb097_wpp_notmem_0111 (k : Var) (m : Var) : (nb097_alpha_dummy_039 k m) ∉ ((syn_cnnc)).fv := by
  simpa only [nb097_alpha_dummy_039, fv_syn_cnnc] using (nb097_compact_fv_empty_0035 k m)

theorem nb097_compact_envfresh_0007 (C : Class) (k : Var) (m : Var) (F : Class) : TEnvFresh [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb097_alpha_dummy_020 C F) (nb097_alpha_dummy_021 k m) (nb097_wpp_notmem_0070 C F) (nb097_wpp_notmem_0071 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_016 C F) (nb097_alpha_dummy_018 k m) (nb097_wpp_notmem_0072 C F) (nb097_wpp_notmem_0073 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_017 C F) (nb097_alpha_dummy_019 k m) (nb097_wpp_notmem_0074 C F) (nb097_wpp_notmem_0075 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_042 C F) (nb097_alpha_dummy_043 k m) (nb097_wpp_notmem_0106 C F) (nb097_wpp_notmem_0107 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_040 C F) (nb097_alpha_dummy_041 k m) (nb097_wpp_notmem_0108 C F) (nb097_wpp_notmem_0109 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_009 C F) (nb097_alpha_dummy_011 k m) (nb097_wpp_notmem_0076 C F) (nb097_wpp_notmem_0077 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_008 C F) (nb097_alpha_dummy_010 k m) (nb097_wpp_notmem_0078 C F) (nb097_wpp_notmem_0079 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_038 C F) (nb097_alpha_dummy_039 k m) (nb097_wpp_notmem_0110 C F) (nb097_wpp_notmem_0111 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_012 C F) (nb097_alpha_dummy_013 k m) (nb097_wpp_notmem_0082 C F) (nb097_wpp_notmem_0083 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0084 C F) (nb097_wpp_notmem_0085 k) (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0086 C F) (nb097_wpp_notmem_0087 m) (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F) (nb097_wpp_notmem_0088 C F) (nb097_wpp_notmem_0089 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F) (nb097_wpp_notmem_0090 C F) (nb097_wpp_notmem_0091 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0092 C F) (nb097_wpp_notmem_0093 C k m F) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb097_wpp_refl_0007 (C : Class) (k : Var) (m : Var) (F : Class) : TReflOn [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0007 C k m F)

theorem nb097_wpp_notmem_0112 (C : Class) (F : Class) : (nb097_alpha_dummy_040 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_040, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0032 C F)

theorem nb097_wpp_notmem_0113 (k : Var) (m : Var) : (nb097_alpha_dummy_041 k m) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_041, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0033 k m)

theorem nb097_wpp_notmem_0114 (C : Class) (F : Class) : (nb097_alpha_dummy_009 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0012 C F)

theorem nb097_wpp_notmem_0115 (k : Var) (m : Var) : (nb097_alpha_dummy_011 k m) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_011, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0013 k m)

theorem nb097_wpp_notmem_0116 (C : Class) (F : Class) : (nb097_alpha_dummy_008 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0014 C F)

theorem nb097_wpp_notmem_0117 (k : Var) (m : Var) : (nb097_alpha_dummy_010 k m) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0015 k m)

theorem nb097_wpp_notmem_0118 (C : Class) (F : Class) : (nb097_alpha_dummy_038 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_038, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0034 C F)

theorem nb097_wpp_notmem_0119 (k : Var) (m : Var) : (nb097_alpha_dummy_039 k m) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_039, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0035 k m)

theorem nb097_wpp_notmem_0120 (C : Class) (F : Class) : (nb097_alpha_dummy_012 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_012, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0018 C F)

theorem nb097_wpp_notmem_0121 (k : Var) (m : Var) : (nb097_alpha_dummy_013 k m) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_013, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0019 k m)

theorem nb097_wpp_notmem_0122 (C : Class) (F : Class) : (nb097_alpha_dummy_000 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0020 C F)

theorem nb097_wpp_notmem_0123 (k : Var) : k ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0021 k)

theorem nb097_wpp_notmem_0124 (C : Class) (F : Class) : (nb097_alpha_dummy_001 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0022 C F)

theorem nb097_wpp_notmem_0125 (m : Var) : m ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0023 m)

theorem nb097_wpp_notmem_0126 (C : Class) (F : Class) : (nb097_alpha_dummy_002 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0024 C F)

theorem nb097_wpp_notmem_0127 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_003 C k m F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0025 C k m F)

theorem nb097_wpp_notmem_0128 (C : Class) (F : Class) : (nb097_alpha_dummy_005 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0026 C F)

theorem nb097_wpp_notmem_0129 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_007 C k m F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0027 C k m F)

theorem nb097_wpp_notmem_0130 (C : Class) (F : Class) : (nb097_alpha_dummy_004 C F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0028 C F)

theorem nb097_wpp_notmem_0131 (C : Class) (k : Var) (m : Var) (F : Class) : (nb097_alpha_dummy_006 C k m F) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb097_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb097_compact_fv_empty_0029 C k m F)

theorem nb097_compact_envfresh_0008 (C : Class) (k : Var) (m : Var) (F : Class) : TEnvFresh [((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb097_alpha_dummy_040 C F) (nb097_alpha_dummy_041 k m) (nb097_wpp_notmem_0112 C F) (nb097_wpp_notmem_0113 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_009 C F) (nb097_alpha_dummy_011 k m) (nb097_wpp_notmem_0114 C F) (nb097_wpp_notmem_0115 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_008 C F) (nb097_alpha_dummy_010 k m) (nb097_wpp_notmem_0116 C F) (nb097_wpp_notmem_0117 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_038 C F) (nb097_alpha_dummy_039 k m) (nb097_wpp_notmem_0118 C F) (nb097_wpp_notmem_0119 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_012 C F) (nb097_alpha_dummy_013 k m) (nb097_wpp_notmem_0120 C F) (nb097_wpp_notmem_0121 k m) (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0122 C F) (nb097_wpp_notmem_0123 k) (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0124 C F) (nb097_wpp_notmem_0125 m) (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F) (nb097_wpp_notmem_0126 C F) (nb097_wpp_notmem_0127 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F) (nb097_wpp_notmem_0128 C F) (nb097_wpp_notmem_0129 C k m F) (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0130 C F) (nb097_wpp_notmem_0131 C k m F) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))

noncomputable def nb097_wpp_refl_0008 (C : Class) (k : Var) (m : Var) (F : Class) : TReflOn [((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0008 C k m F)

noncomputable def nb097_split_alpha_0000 (C : Class) (k : Var) (m : Var) (F : Class) : TAlphaWff [((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (Wff.imp (Wff.classMem (Class.cv (nb097_alpha_dummy_009 C F)) (Class.cv (nb097_alpha_dummy_000 C F))) (Wff.neg (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb097_alpha_dummy_011 k m)) (Class.cv k)) (Wff.neg (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m)) (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0032 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0033 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0029 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0031 k m) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪ ((Class.cv (nb097_alpha_dummy_000 C F))).fv) (by decide)) (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0006 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0007 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0006 C F) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0007 k m) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0036 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0037 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0034 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0035 k m) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_009 C F))).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_011 k m))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0010 C F) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0011 k m) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0010 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0011 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0008 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0009 k m) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c1c) (nb097_wpp_refl_0005 C k m F))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0014 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0015 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0012 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0013 k m) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0018 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0019 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0016 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0017 k m) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0014 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0015 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0012 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0013 k m) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0018 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0019 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0016 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0017 k m) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c0) (nb097_wpp_refl_0006 C k m F))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0022 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0023 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0020 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0021 k m) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0022 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0023 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0020 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0021 k m) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0026 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0027 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0024 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0025 k m) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0026 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0027 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0024 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0025 k m) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0008 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0009 k m) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_cnnc) (nb097_wpp_refl_0007 C k m F))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0008 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0009 k m) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0008 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0009 k m) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_cnnc) (nb097_wpp_refl_0007 C k m F)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0006 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0007 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0006 C F) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0007 k m) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0036 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0037 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0034 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0035 k m) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_009 C F))).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_011 k m))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0010 C F) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0011 k m) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0010 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0011 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0008 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0009 k m) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c1c) (nb097_wpp_refl_0005 C k m F))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0014 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0015 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0012 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0013 k m) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0018 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0019 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0016 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0017 k m) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0014 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0015 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0012 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0013 k m) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0018 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0019 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0016 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0017 k m) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)), ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)), ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)), ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c0) (nb097_wpp_refl_0006 C k m F))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0022 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0023 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0020 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0021 k m) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0022 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0023 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0020 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0021 k m) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0026 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0027 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0024 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0025 k m) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0026 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0027 k m) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0024 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0025 k m) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0008 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0009 k m) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_cnnc) (nb097_wpp_refl_0007 C k m F))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0008 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0009 k m) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0008 C F) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0009 k m) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)), ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)), ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)), ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)), ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_cnnc) (nb097_wpp_refl_0007 C k m F)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)), ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)), ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)), ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)), ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)), ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)), ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)), ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_ccompl (syn_csn (syn_c0c))) (nb097_wpp_refl_0008 C k m F)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
