import NAR4C056C001Part011

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

noncomputable def nb056_split_alpha_0020 (f : Var) : TAlphaWff [((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)), ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)), ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classEq (Class.cv (nb056_alpha_dummy_089)) (syn_cop (Class.cv (nb056_alpha_dummy_085)) (Class.cv (nb056_alpha_dummy_086)))) (Wff.neg (syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_085))))) (Wff.imp (Wff.classEq (Class.cv (nb056_alpha_dummy_090 f)) (syn_cop (Class.cv (nb056_alpha_dummy_087 f)) (Class.cv (nb056_alpha_dummy_088 f)))) (Wff.neg (syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f) (Class.cv (nb056_alpha_dummy_087 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0082) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0083 f) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0080) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0081 f) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0089 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0085) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0011 f))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0089 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0085) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0011 f))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0014 f))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0127 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0123) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0125 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0016 f))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0126) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0127 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0123) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0125 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0016 f))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0019 f)))))))))) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0170) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0171 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0169 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 2)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 2)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0165) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0167 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0162) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0163 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0160) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0161 f) 0)) (TAlphaVar.here _ _ _))))))))))))))

theorem nb056_compact_fv_empty_0124 : (nb056_alpha_dummy_179) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0408 : (nb056_alpha_dummy_179) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_179, fv_syn_c1c] using (nb056_compact_fv_empty_0124)

theorem nb056_compact_fv_empty_0125 (f : Var) : (nb056_alpha_dummy_182 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0409 (f : Var) : (nb056_alpha_dummy_182 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_182, fv_syn_c1c] using (nb056_compact_fv_empty_0125 f)

theorem nb056_compact_fv_empty_0126 : (nb056_alpha_dummy_178) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0410 : (nb056_alpha_dummy_178) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_178, fv_syn_c1c] using (nb056_compact_fv_empty_0126)

theorem nb056_compact_fv_empty_0127 (f : Var) : (nb056_alpha_dummy_181 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0411 (f : Var) : (nb056_alpha_dummy_181 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_181, fv_syn_c1c] using (nb056_compact_fv_empty_0127 f)

theorem nb056_compact_fv_empty_0128 : (nb056_alpha_dummy_177) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0412 : (nb056_alpha_dummy_177) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_177, fv_syn_c1c] using (nb056_compact_fv_empty_0128)

theorem nb056_compact_fv_empty_0129 (f : Var) : (nb056_alpha_dummy_180 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0413 (f : Var) : (nb056_alpha_dummy_180 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_180, fv_syn_c1c] using (nb056_compact_fv_empty_0129 f)

theorem nb056_compact_fv_empty_0130 : (nb056_alpha_dummy_175) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0414 : (nb056_alpha_dummy_175) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_175, fv_syn_c1c] using (nb056_compact_fv_empty_0130)

theorem nb056_compact_fv_empty_0131 (f : Var) : (nb056_alpha_dummy_176 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0415 (f : Var) : (nb056_alpha_dummy_176 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_176, fv_syn_c1c] using (nb056_compact_fv_empty_0131 f)

theorem nb056_compact_fv_empty_0132 : (nb056_alpha_dummy_171) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0416 : (nb056_alpha_dummy_171) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_171, fv_syn_c1c] using (nb056_compact_fv_empty_0132)

theorem nb056_compact_fv_empty_0133 (f : Var) : (nb056_alpha_dummy_173 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0417 (f : Var) : (nb056_alpha_dummy_173 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_173, fv_syn_c1c] using (nb056_compact_fv_empty_0133 f)

theorem nb056_compact_fv_empty_0134 : (nb056_alpha_dummy_172) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0418 : (nb056_alpha_dummy_172) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_172, fv_syn_c1c] using (nb056_compact_fv_empty_0134)

theorem nb056_compact_fv_empty_0135 (f : Var) : (nb056_alpha_dummy_174 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0419 (f : Var) : (nb056_alpha_dummy_174 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_174, fv_syn_c1c] using (nb056_compact_fv_empty_0135 f)

theorem nb056_compact_fv_empty_0136 : (nb056_alpha_dummy_164) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0420 : (nb056_alpha_dummy_164) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_164, fv_syn_c1c] using (nb056_compact_fv_empty_0136)

theorem nb056_compact_fv_empty_0137 (f : Var) : (nb056_alpha_dummy_166 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0421 (f : Var) : (nb056_alpha_dummy_166 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_166, fv_syn_c1c] using (nb056_compact_fv_empty_0137 f)

theorem nb056_compact_fv_empty_0138 : (nb056_alpha_dummy_163) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0422 : (nb056_alpha_dummy_163) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_163, fv_syn_c1c] using (nb056_compact_fv_empty_0138)

theorem nb056_compact_fv_empty_0139 (f : Var) : (nb056_alpha_dummy_165 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0423 (f : Var) : (nb056_alpha_dummy_165 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_165, fv_syn_c1c] using (nb056_compact_fv_empty_0139 f)

theorem nb056_compact_fv_empty_0140 : (nb056_alpha_dummy_169) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0424 : (nb056_alpha_dummy_169) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_169, fv_syn_c1c] using (nb056_compact_fv_empty_0140)

theorem nb056_compact_fv_empty_0141 (f : Var) : (nb056_alpha_dummy_170 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0425 (f : Var) : (nb056_alpha_dummy_170 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_170, fv_syn_c1c] using (nb056_compact_fv_empty_0141 f)

theorem nb056_compact_fv_empty_0142 : (nb056_alpha_dummy_167) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0426 : (nb056_alpha_dummy_167) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_167, fv_syn_c1c] using (nb056_compact_fv_empty_0142)

theorem nb056_compact_fv_empty_0143 (f : Var) : (nb056_alpha_dummy_168 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0427 (f : Var) : (nb056_alpha_dummy_168 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_168, fv_syn_c1c] using (nb056_compact_fv_empty_0143 f)

theorem nb056_compact_envfresh_0028 (f : Var) : TEnvFresh [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_179) (nb056_alpha_dummy_182 f) (nb056_wpp_notmem_0408) (nb056_wpp_notmem_0409 f) (TEnvFresh.consFresh (nb056_alpha_dummy_178) (nb056_alpha_dummy_181 f) (nb056_wpp_notmem_0410) (nb056_wpp_notmem_0411 f) (TEnvFresh.consFresh (nb056_alpha_dummy_177) (nb056_alpha_dummy_180 f) (nb056_wpp_notmem_0412) (nb056_wpp_notmem_0413 f) (TEnvFresh.consFresh (nb056_alpha_dummy_175) (nb056_alpha_dummy_176 f) (nb056_wpp_notmem_0414) (nb056_wpp_notmem_0415 f) (TEnvFresh.consFresh (nb056_alpha_dummy_171) (nb056_alpha_dummy_173 f) (nb056_wpp_notmem_0416) (nb056_wpp_notmem_0417 f) (TEnvFresh.consFresh (nb056_alpha_dummy_172) (nb056_alpha_dummy_174 f) (nb056_wpp_notmem_0418) (nb056_wpp_notmem_0419 f) (TEnvFresh.consFresh (nb056_alpha_dummy_164) (nb056_alpha_dummy_166 f) (nb056_wpp_notmem_0420) (nb056_wpp_notmem_0421 f) (TEnvFresh.consFresh (nb056_alpha_dummy_163) (nb056_alpha_dummy_165 f) (nb056_wpp_notmem_0422) (nb056_wpp_notmem_0423 f) (TEnvFresh.consFresh (nb056_alpha_dummy_169) (nb056_alpha_dummy_170 f) (nb056_wpp_notmem_0424) (nb056_wpp_notmem_0425 f) (TEnvFresh.consFresh (nb056_alpha_dummy_167) (nb056_alpha_dummy_168 f) (nb056_wpp_notmem_0426) (nb056_wpp_notmem_0427 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0150) (nb056_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0020) (nb056_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0022) (nb056_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0024) (nb056_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0026) (nb056_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0028) (nb056_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0030) (nb056_wpp_notmem_0031 f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb056_wpp_refl_0028 (f : Var) : TReflOn [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0028 f)

theorem nb056_wpp_notmem_0428 : (nb056_alpha_dummy_179) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_179, fv_syn_c0] using (nb056_compact_fv_empty_0124)

theorem nb056_wpp_notmem_0429 (f : Var) : (nb056_alpha_dummy_182 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_182, fv_syn_c0] using (nb056_compact_fv_empty_0125 f)

theorem nb056_wpp_notmem_0430 : (nb056_alpha_dummy_178) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_178, fv_syn_c0] using (nb056_compact_fv_empty_0126)

theorem nb056_wpp_notmem_0431 (f : Var) : (nb056_alpha_dummy_181 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_181, fv_syn_c0] using (nb056_compact_fv_empty_0127 f)

theorem nb056_wpp_notmem_0432 : (nb056_alpha_dummy_177) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_177, fv_syn_c0] using (nb056_compact_fv_empty_0128)

theorem nb056_wpp_notmem_0433 (f : Var) : (nb056_alpha_dummy_180 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_180, fv_syn_c0] using (nb056_compact_fv_empty_0129 f)

theorem nb056_wpp_notmem_0434 : (nb056_alpha_dummy_175) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_175, fv_syn_c0] using (nb056_compact_fv_empty_0130)

theorem nb056_wpp_notmem_0435 (f : Var) : (nb056_alpha_dummy_176 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_176, fv_syn_c0] using (nb056_compact_fv_empty_0131 f)

theorem nb056_wpp_notmem_0436 : (nb056_alpha_dummy_171) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_171, fv_syn_c0] using (nb056_compact_fv_empty_0132)

theorem nb056_wpp_notmem_0437 (f : Var) : (nb056_alpha_dummy_173 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_173, fv_syn_c0] using (nb056_compact_fv_empty_0133 f)

theorem nb056_wpp_notmem_0438 : (nb056_alpha_dummy_172) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_172, fv_syn_c0] using (nb056_compact_fv_empty_0134)

theorem nb056_wpp_notmem_0439 (f : Var) : (nb056_alpha_dummy_174 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_174, fv_syn_c0] using (nb056_compact_fv_empty_0135 f)

theorem nb056_wpp_notmem_0440 : (nb056_alpha_dummy_164) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_164, fv_syn_c0] using (nb056_compact_fv_empty_0136)

theorem nb056_wpp_notmem_0441 (f : Var) : (nb056_alpha_dummy_166 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_166, fv_syn_c0] using (nb056_compact_fv_empty_0137 f)

theorem nb056_wpp_notmem_0442 : (nb056_alpha_dummy_163) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_163, fv_syn_c0] using (nb056_compact_fv_empty_0138)

theorem nb056_wpp_notmem_0443 (f : Var) : (nb056_alpha_dummy_165 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_165, fv_syn_c0] using (nb056_compact_fv_empty_0139 f)

theorem nb056_wpp_notmem_0444 : (nb056_alpha_dummy_169) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_169, fv_syn_c0] using (nb056_compact_fv_empty_0140)

theorem nb056_wpp_notmem_0445 (f : Var) : (nb056_alpha_dummy_170 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_170, fv_syn_c0] using (nb056_compact_fv_empty_0141 f)

theorem nb056_wpp_notmem_0446 : (nb056_alpha_dummy_167) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_167, fv_syn_c0] using (nb056_compact_fv_empty_0142)

theorem nb056_wpp_notmem_0447 (f : Var) : (nb056_alpha_dummy_168 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_168, fv_syn_c0] using (nb056_compact_fv_empty_0143 f)

theorem nb056_compact_envfresh_0029 (f : Var) : TEnvFresh [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_179) (nb056_alpha_dummy_182 f) (nb056_wpp_notmem_0428) (nb056_wpp_notmem_0429 f) (TEnvFresh.consFresh (nb056_alpha_dummy_178) (nb056_alpha_dummy_181 f) (nb056_wpp_notmem_0430) (nb056_wpp_notmem_0431 f) (TEnvFresh.consFresh (nb056_alpha_dummy_177) (nb056_alpha_dummy_180 f) (nb056_wpp_notmem_0432) (nb056_wpp_notmem_0433 f) (TEnvFresh.consFresh (nb056_alpha_dummy_175) (nb056_alpha_dummy_176 f) (nb056_wpp_notmem_0434) (nb056_wpp_notmem_0435 f) (TEnvFresh.consFresh (nb056_alpha_dummy_171) (nb056_alpha_dummy_173 f) (nb056_wpp_notmem_0436) (nb056_wpp_notmem_0437 f) (TEnvFresh.consFresh (nb056_alpha_dummy_172) (nb056_alpha_dummy_174 f) (nb056_wpp_notmem_0438) (nb056_wpp_notmem_0439 f) (TEnvFresh.consFresh (nb056_alpha_dummy_164) (nb056_alpha_dummy_166 f) (nb056_wpp_notmem_0440) (nb056_wpp_notmem_0441 f) (TEnvFresh.consFresh (nb056_alpha_dummy_163) (nb056_alpha_dummy_165 f) (nb056_wpp_notmem_0442) (nb056_wpp_notmem_0443 f) (TEnvFresh.consFresh (nb056_alpha_dummy_169) (nb056_alpha_dummy_170 f) (nb056_wpp_notmem_0444) (nb056_wpp_notmem_0445 f) (TEnvFresh.consFresh (nb056_alpha_dummy_167) (nb056_alpha_dummy_168 f) (nb056_wpp_notmem_0446) (nb056_wpp_notmem_0447 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0172) (nb056_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0052) (nb056_wpp_notmem_0053 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0054) (nb056_wpp_notmem_0055 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0056) (nb056_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0058) (nb056_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0060) (nb056_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0062) (nb056_wpp_notmem_0063 f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb056_wpp_refl_0029 (f : Var) : TReflOn [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0029 f)

noncomputable def nb056_split_alpha_0021 (f : Var) : TAlphaWff [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_177)) (syn_cun (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_180 f)) (syn_cun (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c0) (nb056_wpp_refl_0029 f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb056_wpp_notmem_0448 : (nb056_alpha_dummy_175) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_175, fv_syn_cnnc] using (nb056_compact_fv_empty_0130)

theorem nb056_wpp_notmem_0449 (f : Var) : (nb056_alpha_dummy_176 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_176, fv_syn_cnnc] using (nb056_compact_fv_empty_0131 f)

theorem nb056_wpp_notmem_0450 : (nb056_alpha_dummy_171) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_171, fv_syn_cnnc] using (nb056_compact_fv_empty_0132)

theorem nb056_wpp_notmem_0451 (f : Var) : (nb056_alpha_dummy_173 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_173, fv_syn_cnnc] using (nb056_compact_fv_empty_0133 f)

theorem nb056_wpp_notmem_0452 : (nb056_alpha_dummy_172) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_172, fv_syn_cnnc] using (nb056_compact_fv_empty_0134)

theorem nb056_wpp_notmem_0453 (f : Var) : (nb056_alpha_dummy_174 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_174, fv_syn_cnnc] using (nb056_compact_fv_empty_0135 f)

theorem nb056_wpp_notmem_0454 : (nb056_alpha_dummy_164) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_164, fv_syn_cnnc] using (nb056_compact_fv_empty_0136)

theorem nb056_wpp_notmem_0455 (f : Var) : (nb056_alpha_dummy_166 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_166, fv_syn_cnnc] using (nb056_compact_fv_empty_0137 f)

theorem nb056_wpp_notmem_0456 : (nb056_alpha_dummy_163) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_163, fv_syn_cnnc] using (nb056_compact_fv_empty_0138)

theorem nb056_wpp_notmem_0457 (f : Var) : (nb056_alpha_dummy_165 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_165, fv_syn_cnnc] using (nb056_compact_fv_empty_0139 f)

theorem nb056_wpp_notmem_0458 : (nb056_alpha_dummy_169) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_169, fv_syn_cnnc] using (nb056_compact_fv_empty_0140)

theorem nb056_wpp_notmem_0459 (f : Var) : (nb056_alpha_dummy_170 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_170, fv_syn_cnnc] using (nb056_compact_fv_empty_0141 f)

theorem nb056_wpp_notmem_0460 : (nb056_alpha_dummy_167) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_167, fv_syn_cnnc] using (nb056_compact_fv_empty_0142)

theorem nb056_wpp_notmem_0461 (f : Var) : (nb056_alpha_dummy_168 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_168, fv_syn_cnnc] using (nb056_compact_fv_empty_0143 f)

theorem nb056_compact_envfresh_0030 (f : Var) : TEnvFresh [((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_175) (nb056_alpha_dummy_176 f) (nb056_wpp_notmem_0448) (nb056_wpp_notmem_0449 f) (TEnvFresh.consFresh (nb056_alpha_dummy_171) (nb056_alpha_dummy_173 f) (nb056_wpp_notmem_0450) (nb056_wpp_notmem_0451 f) (TEnvFresh.consFresh (nb056_alpha_dummy_172) (nb056_alpha_dummy_174 f) (nb056_wpp_notmem_0452) (nb056_wpp_notmem_0453 f) (TEnvFresh.consFresh (nb056_alpha_dummy_164) (nb056_alpha_dummy_166 f) (nb056_wpp_notmem_0454) (nb056_wpp_notmem_0455 f) (TEnvFresh.consFresh (nb056_alpha_dummy_163) (nb056_alpha_dummy_165 f) (nb056_wpp_notmem_0456) (nb056_wpp_notmem_0457 f) (TEnvFresh.consFresh (nb056_alpha_dummy_169) (nb056_alpha_dummy_170 f) (nb056_wpp_notmem_0458) (nb056_wpp_notmem_0459 f) (TEnvFresh.consFresh (nb056_alpha_dummy_167) (nb056_alpha_dummy_168 f) (nb056_wpp_notmem_0460) (nb056_wpp_notmem_0461 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0188) (nb056_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0078) (nb056_wpp_notmem_0079 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0080) (nb056_wpp_notmem_0081 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0082) (nb056_wpp_notmem_0083 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0084) (nb056_wpp_notmem_0085 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0086) (nb056_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0088) (nb056_wpp_notmem_0089 f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb056_wpp_refl_0030 (f : Var) : TReflOn [((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0030 f)

noncomputable def nb056_split_alpha_0022 (f : Var) : TAlphaWff [((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.classEq (Class.cv (nb056_alpha_dummy_163)) (syn_cphi (Class.cv (nb056_alpha_dummy_164)))) (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_164))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_166 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c1c) (nb056_wpp_refl_0028 f))) (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0021 f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0030 f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0030 f))))))))))))))))))

theorem nb056_compact_fv_empty_0144 : (nb056_alpha_dummy_197) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0462 : (nb056_alpha_dummy_197) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_197, fv_syn_c1c] using (nb056_compact_fv_empty_0144)

theorem nb056_compact_fv_empty_0145 (f : Var) : (nb056_alpha_dummy_198 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0463 (f : Var) : (nb056_alpha_dummy_198 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_198, fv_syn_c1c] using (nb056_compact_fv_empty_0145 f)

theorem nb056_compact_fv_empty_0146 : (nb056_alpha_dummy_195) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0464 : (nb056_alpha_dummy_195) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_195, fv_syn_c1c] using (nb056_compact_fv_empty_0146)

theorem nb056_compact_fv_empty_0147 (f : Var) : (nb056_alpha_dummy_196 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0465 (f : Var) : (nb056_alpha_dummy_196 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_196, fv_syn_c1c] using (nb056_compact_fv_empty_0147 f)

theorem nb056_compact_fv_empty_0148 : (nb056_alpha_dummy_193) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0466 : (nb056_alpha_dummy_193) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_193, fv_syn_c1c] using (nb056_compact_fv_empty_0148)

theorem nb056_compact_fv_empty_0149 (f : Var) : (nb056_alpha_dummy_194 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0467 (f : Var) : (nb056_alpha_dummy_194 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_194, fv_syn_c1c] using (nb056_compact_fv_empty_0149 f)

theorem nb056_compact_envfresh_0031 (f : Var) : TEnvFresh [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)), ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_179) (nb056_alpha_dummy_182 f) (nb056_wpp_notmem_0408) (nb056_wpp_notmem_0409 f) (TEnvFresh.consFresh (nb056_alpha_dummy_178) (nb056_alpha_dummy_181 f) (nb056_wpp_notmem_0410) (nb056_wpp_notmem_0411 f) (TEnvFresh.consFresh (nb056_alpha_dummy_177) (nb056_alpha_dummy_180 f) (nb056_wpp_notmem_0412) (nb056_wpp_notmem_0413 f) (TEnvFresh.consFresh (nb056_alpha_dummy_175) (nb056_alpha_dummy_176 f) (nb056_wpp_notmem_0414) (nb056_wpp_notmem_0415 f) (TEnvFresh.consFresh (nb056_alpha_dummy_171) (nb056_alpha_dummy_173 f) (nb056_wpp_notmem_0416) (nb056_wpp_notmem_0417 f) (TEnvFresh.consFresh (nb056_alpha_dummy_172) (nb056_alpha_dummy_174 f) (nb056_wpp_notmem_0418) (nb056_wpp_notmem_0419 f) (TEnvFresh.consFresh (nb056_alpha_dummy_197) (nb056_alpha_dummy_198 f) (nb056_wpp_notmem_0462) (nb056_wpp_notmem_0463 f) (TEnvFresh.consFresh (nb056_alpha_dummy_195) (nb056_alpha_dummy_196 f) (nb056_wpp_notmem_0464) (nb056_wpp_notmem_0465 f) (TEnvFresh.consFresh (nb056_alpha_dummy_164) (nb056_alpha_dummy_166 f) (nb056_wpp_notmem_0420) (nb056_wpp_notmem_0421 f) (TEnvFresh.consFresh (nb056_alpha_dummy_163) (nb056_alpha_dummy_165 f) (nb056_wpp_notmem_0422) (nb056_wpp_notmem_0423 f) (TEnvFresh.consFresh (nb056_alpha_dummy_193) (nb056_alpha_dummy_194 f) (nb056_wpp_notmem_0466) (nb056_wpp_notmem_0467 f) (TEnvFresh.consFresh (nb056_alpha_dummy_167) (nb056_alpha_dummy_168 f) (nb056_wpp_notmem_0426) (nb056_wpp_notmem_0427 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0150) (nb056_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0020) (nb056_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0022) (nb056_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0024) (nb056_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0026) (nb056_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0028) (nb056_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0030) (nb056_wpp_notmem_0031 f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb056_wpp_refl_0031 (f : Var) : TReflOn [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)), ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0031 f)

theorem nb056_wpp_notmem_0468 : (nb056_alpha_dummy_197) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_197, fv_syn_c0] using (nb056_compact_fv_empty_0144)

theorem nb056_wpp_notmem_0469 (f : Var) : (nb056_alpha_dummy_198 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_198, fv_syn_c0] using (nb056_compact_fv_empty_0145 f)

theorem nb056_wpp_notmem_0470 : (nb056_alpha_dummy_195) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_195, fv_syn_c0] using (nb056_compact_fv_empty_0146)

theorem nb056_wpp_notmem_0471 (f : Var) : (nb056_alpha_dummy_196 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_196, fv_syn_c0] using (nb056_compact_fv_empty_0147 f)

theorem nb056_wpp_notmem_0472 : (nb056_alpha_dummy_193) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_193, fv_syn_c0] using (nb056_compact_fv_empty_0148)

theorem nb056_wpp_notmem_0473 (f : Var) : (nb056_alpha_dummy_194 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_194, fv_syn_c0] using (nb056_compact_fv_empty_0149 f)

theorem nb056_compact_envfresh_0032 (f : Var) : TEnvFresh [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)), ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_179) (nb056_alpha_dummy_182 f) (nb056_wpp_notmem_0428) (nb056_wpp_notmem_0429 f) (TEnvFresh.consFresh (nb056_alpha_dummy_178) (nb056_alpha_dummy_181 f) (nb056_wpp_notmem_0430) (nb056_wpp_notmem_0431 f) (TEnvFresh.consFresh (nb056_alpha_dummy_177) (nb056_alpha_dummy_180 f) (nb056_wpp_notmem_0432) (nb056_wpp_notmem_0433 f) (TEnvFresh.consFresh (nb056_alpha_dummy_175) (nb056_alpha_dummy_176 f) (nb056_wpp_notmem_0434) (nb056_wpp_notmem_0435 f) (TEnvFresh.consFresh (nb056_alpha_dummy_171) (nb056_alpha_dummy_173 f) (nb056_wpp_notmem_0436) (nb056_wpp_notmem_0437 f) (TEnvFresh.consFresh (nb056_alpha_dummy_172) (nb056_alpha_dummy_174 f) (nb056_wpp_notmem_0438) (nb056_wpp_notmem_0439 f) (TEnvFresh.consFresh (nb056_alpha_dummy_197) (nb056_alpha_dummy_198 f) (nb056_wpp_notmem_0468) (nb056_wpp_notmem_0469 f) (TEnvFresh.consFresh (nb056_alpha_dummy_195) (nb056_alpha_dummy_196 f) (nb056_wpp_notmem_0470) (nb056_wpp_notmem_0471 f) (TEnvFresh.consFresh (nb056_alpha_dummy_164) (nb056_alpha_dummy_166 f) (nb056_wpp_notmem_0440) (nb056_wpp_notmem_0441 f) (TEnvFresh.consFresh (nb056_alpha_dummy_163) (nb056_alpha_dummy_165 f) (nb056_wpp_notmem_0442) (nb056_wpp_notmem_0443 f) (TEnvFresh.consFresh (nb056_alpha_dummy_193) (nb056_alpha_dummy_194 f) (nb056_wpp_notmem_0472) (nb056_wpp_notmem_0473 f) (TEnvFresh.consFresh (nb056_alpha_dummy_167) (nb056_alpha_dummy_168 f) (nb056_wpp_notmem_0446) (nb056_wpp_notmem_0447 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0172) (nb056_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0052) (nb056_wpp_notmem_0053 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0054) (nb056_wpp_notmem_0055 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0056) (nb056_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0058) (nb056_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0060) (nb056_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0062) (nb056_wpp_notmem_0063 f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb056_wpp_refl_0032 (f : Var) : TReflOn [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)), ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)), ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)), ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)), ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)), ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)), ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)), ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)), ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)), ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)), ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)), ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0032 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
