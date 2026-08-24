import NAR4C057C001Part005

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

theorem nb057_support_mem_0103 (f : Var) : (nb057_alpha_dummy_107 f) ∈ (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0104 : (nb057_alpha_dummy_103) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0105 (f : Var) : (nb057_alpha_dummy_106 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0106 : (nb057_alpha_dummy_103) ∈ (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_103))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0107 (f : Var) : (nb057_alpha_dummy_106 f) ∈ (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_106 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0108 : (nb057_alpha_dummy_104) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0109 (f : Var) : (nb057_alpha_dummy_107 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0110 : (nb057_alpha_dummy_104) ∈ (((Class.cv (nb057_alpha_dummy_104))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0111 (f : Var) : (nb057_alpha_dummy_107 f) ∈ (((Class.cv (nb057_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0112 : (nb057_alpha_dummy_046) ∈ (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0113 : (nb057_alpha_dummy_046) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0114 (f : Var) : (nb057_alpha_dummy_049 f) ∈ (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0115 (f : Var) : (nb057_alpha_dummy_049 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0116 : (nb057_alpha_dummy_046) ∈ (((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088) (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_088)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0117 (f : Var) : (nb057_alpha_dummy_049 f) ∈ (((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f) (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0118 : (nb057_alpha_dummy_089) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_089))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0119 (f : Var) : (nb057_alpha_dummy_091 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0120 : (nb057_alpha_dummy_089) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0121 (f : Var) : (nb057_alpha_dummy_091 f) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0122 : (nb057_alpha_dummy_124) ∈ (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_124)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0123 (f : Var) : (nb057_alpha_dummy_126 f) ∈ (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_126 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0124 : (nb057_alpha_dummy_125) ∈ (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_124)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0125 (f : Var) : (nb057_alpha_dummy_127 f) ∈ (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_126 f)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0126 : (nb057_alpha_dummy_124) ∈ (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0127 : (nb057_alpha_dummy_124) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0128 (f : Var) : (nb057_alpha_dummy_126 f) ∈ (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0129 (f : Var) : (nb057_alpha_dummy_126 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0130 : (nb057_alpha_dummy_124) ∈ (((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0131 (f : Var) : (nb057_alpha_dummy_126 f) ∈ (((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0132 : (nb057_alpha_dummy_131) ∈ (((Class.cv (nb057_alpha_dummy_131))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0133 (f : Var) : (nb057_alpha_dummy_133 f) ∈ (((Class.cv (nb057_alpha_dummy_133 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0134 : (nb057_alpha_dummy_138) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_138))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0135 (f : Var) : (nb057_alpha_dummy_140 f) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_140 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0136 : (nb057_alpha_dummy_138) ∈ (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0137 (f : Var) : (nb057_alpha_dummy_140 f) ∈ (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0138 : (nb057_alpha_dummy_145) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0139 (f : Var) : (nb057_alpha_dummy_148 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0140 : (nb057_alpha_dummy_145) ∈ (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0141 (f : Var) : (nb057_alpha_dummy_148 f) ∈ (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0142 : (nb057_alpha_dummy_146) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0143 (f : Var) : (nb057_alpha_dummy_149 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0144 : (nb057_alpha_dummy_146) ∈ (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0145 (f : Var) : (nb057_alpha_dummy_149 f) ∈ (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0146 : (nb057_alpha_dummy_145) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0147 (f : Var) : (nb057_alpha_dummy_148 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0148 : (nb057_alpha_dummy_145) ∈ (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_145))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0149 (f : Var) : (nb057_alpha_dummy_148 f) ∈ (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_148 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0150 : (nb057_alpha_dummy_146) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0151 (f : Var) : (nb057_alpha_dummy_149 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0152 : (nb057_alpha_dummy_146) ∈ (((Class.cv (nb057_alpha_dummy_146))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0153 (f : Var) : (nb057_alpha_dummy_149 f) ∈ (((Class.cv (nb057_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0154 : (nb057_alpha_dummy_125) ∈ (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0155 : (nb057_alpha_dummy_125) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0156 (f : Var) : (nb057_alpha_dummy_127 f) ∈ (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0157 (f : Var) : (nb057_alpha_dummy_127 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0158 : (nb057_alpha_dummy_125) ∈ (((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130) (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_130)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0159 (f : Var) : (nb057_alpha_dummy_127 f) ∈ (((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f) (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0160 : (nb057_alpha_dummy_131) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_131))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0161 (f : Var) : (nb057_alpha_dummy_133 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0162 : (nb057_alpha_dummy_131) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0163 (f : Var) : (nb057_alpha_dummy_133 f) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0164 : (nb057_alpha_dummy_125) ∈ (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0165 : (nb057_alpha_dummy_125) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0166 (f : Var) : (nb057_alpha_dummy_127 f) ∈ (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0167 (f : Var) : (nb057_alpha_dummy_127 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0168 : (nb057_alpha_dummy_125) ∈ (((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0169 (f : Var) : (nb057_alpha_dummy_127 f) ∈ (((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0170 : (nb057_alpha_dummy_167) ∈ (((Class.cv (nb057_alpha_dummy_167))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0171 (f : Var) : (nb057_alpha_dummy_169 f) ∈ (((Class.cv (nb057_alpha_dummy_169 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0172 : (nb057_alpha_dummy_174) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_174))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0173 (f : Var) : (nb057_alpha_dummy_176 f) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_176 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0174 : (nb057_alpha_dummy_174) ∈ (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0175 (f : Var) : (nb057_alpha_dummy_176 f) ∈ (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0176 : (nb057_alpha_dummy_181) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0177 (f : Var) : (nb057_alpha_dummy_184 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0178 : (nb057_alpha_dummy_181) ∈ (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0179 (f : Var) : (nb057_alpha_dummy_184 f) ∈ (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0180 : (nb057_alpha_dummy_182) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0181 (f : Var) : (nb057_alpha_dummy_185 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0182 : (nb057_alpha_dummy_182) ∈ (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0183 (f : Var) : (nb057_alpha_dummy_185 f) ∈ (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0184 : (nb057_alpha_dummy_181) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0185 (f : Var) : (nb057_alpha_dummy_184 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0186 : (nb057_alpha_dummy_181) ∈ (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_181))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0187 (f : Var) : (nb057_alpha_dummy_184 f) ∈ (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_184 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0188 : (nb057_alpha_dummy_182) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0189 (f : Var) : (nb057_alpha_dummy_185 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0190 : (nb057_alpha_dummy_182) ∈ (((Class.cv (nb057_alpha_dummy_182))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0191 (f : Var) : (nb057_alpha_dummy_185 f) ∈ (((Class.cv (nb057_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0192 : (nb057_alpha_dummy_124) ∈ (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0193 : (nb057_alpha_dummy_124) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0194 (f : Var) : (nb057_alpha_dummy_126 f) ∈ (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0195 (f : Var) : (nb057_alpha_dummy_126 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0196 : (nb057_alpha_dummy_124) ∈ (((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166) (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124)) (Wff.classEq (Class.cv (nb057_alpha_dummy_166)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0197 (f : Var) : (nb057_alpha_dummy_126 f) ∈ (((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f) (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0198 : (nb057_alpha_dummy_167) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_167))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0199 (f : Var) : (nb057_alpha_dummy_169 f) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0200 : (nb057_alpha_dummy_167) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0201 (f : Var) : (nb057_alpha_dummy_169 f) ∈ (((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv ∪ ((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0202 : (nb057_alpha_dummy_001) ∈ (((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0203 (f : Var) : f ∈ (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0204 : (nb057_alpha_dummy_001) ∈ (((syn_ccom (Class.cv (nb057_alpha_dummy_001)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0205 (f : Var) : f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0206 : (nb057_alpha_dummy_001) ∈ (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0207 : (nb057_alpha_dummy_001) ∈ (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044)) (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046))) (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_045)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb057_support_mem_0208 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0209 (f : Var) : f ∈ (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f)) (Class.cv (nb057_alpha_dummy_049 f))) (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_048 f)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb057_support_mem_0210 : (nb057_alpha_dummy_001) ∈ (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_124)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0211 (f : Var) : f ∈ (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪ ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f) (Class.cv (nb057_alpha_dummy_126 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0212 : (nb057_alpha_dummy_001) ∈ (((Class.cv (nb057_alpha_dummy_001))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0213 (f : Var) : f ∈ (((Class.cv f)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0214 : (nb057_alpha_dummy_046) ∈ (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0215 : (nb057_alpha_dummy_046) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0216 (f : Var) : (nb057_alpha_dummy_049 f) ∈ (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0217 (f : Var) : (nb057_alpha_dummy_049 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0218 : (nb057_alpha_dummy_046) ∈ (((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0219 (f : Var) : (nb057_alpha_dummy_049 f) ∈ (((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0220 : (nb057_alpha_dummy_203) ∈ (((Class.cv (nb057_alpha_dummy_203))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0221 (f : Var) : (nb057_alpha_dummy_205 f) ∈ (((Class.cv (nb057_alpha_dummy_205 f))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0222 : (nb057_alpha_dummy_210) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_210))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0223 (f : Var) : (nb057_alpha_dummy_212 f) ∈ (((Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c))).fv ∪ ((Class.cv (nb057_alpha_dummy_212 f))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0224 : (nb057_alpha_dummy_210) ∈ (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0225 (f : Var) : (nb057_alpha_dummy_212 f) ∈ (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0226 : (nb057_alpha_dummy_217) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0227 (f : Var) : (nb057_alpha_dummy_220 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0228 : (nb057_alpha_dummy_217) ∈ (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0229 (f : Var) : (nb057_alpha_dummy_220 f) ∈ (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0230 : (nb057_alpha_dummy_218) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0231 (f : Var) : (nb057_alpha_dummy_221 f) ∈ (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪ ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0232 : (nb057_alpha_dummy_218) ∈ (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0233 (f : Var) : (nb057_alpha_dummy_221 f) ∈ (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0234 : (nb057_alpha_dummy_217) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0235 (f : Var) : (nb057_alpha_dummy_220 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0236 : (nb057_alpha_dummy_217) ∈ (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_217))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0237 (f : Var) : (nb057_alpha_dummy_220 f) ∈ (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_220 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0238 : (nb057_alpha_dummy_218) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0239 (f : Var) : (nb057_alpha_dummy_221 f) ∈ (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪ ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0240 : (nb057_alpha_dummy_218) ∈ (((Class.cv (nb057_alpha_dummy_218))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0241 (f : Var) : (nb057_alpha_dummy_221 f) ∈ (((Class.cv (nb057_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0242 : (nb057_alpha_dummy_045) ∈ (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0243 : (nb057_alpha_dummy_045) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_202) (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_202)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0244 (f : Var) : (nb057_alpha_dummy_048 f) ∈ (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0245 (f : Var) : (nb057_alpha_dummy_048 f) ∈ (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
