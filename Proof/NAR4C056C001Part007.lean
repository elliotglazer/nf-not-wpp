import NAR4C056C001Part006

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

noncomputable def nb056_split_alpha_0003 (f : Var) : TAlphaWff [((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (Class.cv (nb056_alpha_dummy_014))) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_022)) (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (syn_cnnc)) (syn_cplc (Class.cv (nb056_alpha_dummy_021)) (syn_c1c)) (Class.cv (nb056_alpha_dummy_021)))))) (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (Class.cv (nb056_alpha_dummy_016 f))) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_024 f)) (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb056_alpha_dummy_023 f)) (syn_c1c)) (Class.cv (nb056_alpha_dummy_023 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0040) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0041 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0038) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0039 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_014))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_016 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0015 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0015 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)), ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)), ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)), ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c1c) (nb056_wpp_refl_0003 f))) (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0002 f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0005 f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)), ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)), ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)), ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)), ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0005 f))))))))))))

theorem nb056_wpp_notmem_0108 : (nb056_alpha_dummy_045) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0034)

theorem nb056_wpp_notmem_0109 (f : Var) : (nb056_alpha_dummy_046 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0035 f)

theorem nb056_wpp_notmem_0110 : (nb056_alpha_dummy_014) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_014, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0012)

theorem nb056_wpp_notmem_0111 (f : Var) : (nb056_alpha_dummy_016 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_016, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0013 f)

theorem nb056_wpp_notmem_0112 : (nb056_alpha_dummy_013) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_013, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0014)

theorem nb056_wpp_notmem_0113 (f : Var) : (nb056_alpha_dummy_015 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_015, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0015 f)

theorem nb056_wpp_notmem_0114 : (nb056_alpha_dummy_043) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_043, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0036)

theorem nb056_wpp_notmem_0115 (f : Var) : (nb056_alpha_dummy_044 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0037 f)

theorem nb056_wpp_notmem_0116 : (nb056_alpha_dummy_017) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_017, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0018)

theorem nb056_wpp_notmem_0117 (f : Var) : (nb056_alpha_dummy_018 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_018, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0019 f)

theorem nb056_wpp_notmem_0118 : (nb056_alpha_dummy_006) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0020)

theorem nb056_wpp_notmem_0119 (f : Var) : (nb056_alpha_dummy_009 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0021 f)

theorem nb056_wpp_notmem_0120 : (nb056_alpha_dummy_005) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0022)

theorem nb056_wpp_notmem_0121 (f : Var) : (nb056_alpha_dummy_008 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0023 f)

theorem nb056_wpp_notmem_0122 : (nb056_alpha_dummy_011) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_011, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0024)

theorem nb056_wpp_notmem_0123 (f : Var) : (nb056_alpha_dummy_012 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_012, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0025 f)

theorem nb056_wpp_notmem_0124 : (nb056_alpha_dummy_003) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0026)

theorem nb056_wpp_notmem_0125 (f : Var) : (nb056_alpha_dummy_004 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0027 f)

theorem nb056_wpp_notmem_0126 : (nb056_alpha_dummy_001) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0028)

theorem nb056_wpp_notmem_0127 (f : Var) : (nb056_alpha_dummy_002 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0029 f)

theorem nb056_wpp_notmem_0128 : (nb056_alpha_dummy_000) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb056_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0030)

theorem nb056_wpp_notmem_0129 (f : Var) : f ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb056_compact_fv_empty_0031 f)

theorem nb056_compact_envfresh_0006 (f : Var) : TEnvFresh [((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_045) (nb056_alpha_dummy_046 f) (nb056_wpp_notmem_0108) (nb056_wpp_notmem_0109 f) (TEnvFresh.consFresh (nb056_alpha_dummy_014) (nb056_alpha_dummy_016 f) (nb056_wpp_notmem_0110) (nb056_wpp_notmem_0111 f) (TEnvFresh.consFresh (nb056_alpha_dummy_013) (nb056_alpha_dummy_015 f) (nb056_wpp_notmem_0112) (nb056_wpp_notmem_0113 f) (TEnvFresh.consFresh (nb056_alpha_dummy_043) (nb056_alpha_dummy_044 f) (nb056_wpp_notmem_0114) (nb056_wpp_notmem_0115 f) (TEnvFresh.consFresh (nb056_alpha_dummy_017) (nb056_alpha_dummy_018 f) (nb056_wpp_notmem_0116) (nb056_wpp_notmem_0117 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0118) (nb056_wpp_notmem_0119 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0120) (nb056_wpp_notmem_0121 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0122) (nb056_wpp_notmem_0123 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0124) (nb056_wpp_notmem_0125 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0126) (nb056_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0128) (nb056_wpp_notmem_0129 f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))

noncomputable def nb056_wpp_refl_0006 (f : Var) : TReflOn [((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0006 f)

noncomputable def nb056_split_alpha_0004 (f : Var) : TAlphaWff [((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_043)) (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_043)) (Class.cab (nb056_alpha_dummy_013) (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006)) (Wff.classEq (Class.cv (nb056_alpha_dummy_013)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_044 f)) (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_044 f)) (Class.cab (nb056_alpha_dummy_015 f) (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f)) (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f)) (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0037 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0035 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0003 f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0003 f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (nb056_wpp_refl_0006 f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0037 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0035 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0003 f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0003 f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)), ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)), ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)), ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)), ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (nb056_wpp_refl_0006 f)))))))))))))))))))

theorem nb056_compact_fv_empty_0038 : (nb056_alpha_dummy_065) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0130 : (nb056_alpha_dummy_065) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_065, fv_syn_c1c] using (nb056_compact_fv_empty_0038)

theorem nb056_compact_fv_empty_0039 (f : Var) : (nb056_alpha_dummy_068 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0131 (f : Var) : (nb056_alpha_dummy_068 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_068, fv_syn_c1c] using (nb056_compact_fv_empty_0039 f)

theorem nb056_compact_fv_empty_0040 : (nb056_alpha_dummy_064) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0132 : (nb056_alpha_dummy_064) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_064, fv_syn_c1c] using (nb056_compact_fv_empty_0040)

theorem nb056_compact_fv_empty_0041 (f : Var) : (nb056_alpha_dummy_067 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0133 (f : Var) : (nb056_alpha_dummy_067 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_067, fv_syn_c1c] using (nb056_compact_fv_empty_0041 f)

theorem nb056_compact_fv_empty_0042 : (nb056_alpha_dummy_063) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0134 : (nb056_alpha_dummy_063) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_063, fv_syn_c1c] using (nb056_compact_fv_empty_0042)

theorem nb056_compact_fv_empty_0043 (f : Var) : (nb056_alpha_dummy_066 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0135 (f : Var) : (nb056_alpha_dummy_066 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_066, fv_syn_c1c] using (nb056_compact_fv_empty_0043 f)

theorem nb056_compact_fv_empty_0044 : (nb056_alpha_dummy_061) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0136 : (nb056_alpha_dummy_061) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_061, fv_syn_c1c] using (nb056_compact_fv_empty_0044)

theorem nb056_compact_fv_empty_0045 (f : Var) : (nb056_alpha_dummy_062 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0137 (f : Var) : (nb056_alpha_dummy_062 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_062, fv_syn_c1c] using (nb056_compact_fv_empty_0045 f)

theorem nb056_compact_fv_empty_0046 : (nb056_alpha_dummy_057) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0138 : (nb056_alpha_dummy_057) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_057, fv_syn_c1c] using (nb056_compact_fv_empty_0046)

theorem nb056_compact_fv_empty_0047 (f : Var) : (nb056_alpha_dummy_059 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0139 (f : Var) : (nb056_alpha_dummy_059 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_059, fv_syn_c1c] using (nb056_compact_fv_empty_0047 f)

theorem nb056_compact_fv_empty_0048 : (nb056_alpha_dummy_058) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0140 : (nb056_alpha_dummy_058) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_058, fv_syn_c1c] using (nb056_compact_fv_empty_0048)

theorem nb056_compact_fv_empty_0049 (f : Var) : (nb056_alpha_dummy_060 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0141 (f : Var) : (nb056_alpha_dummy_060 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_060, fv_syn_c1c] using (nb056_compact_fv_empty_0049 f)

theorem nb056_compact_fv_empty_0050 : (nb056_alpha_dummy_050) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0142 : (nb056_alpha_dummy_050) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_050, fv_syn_c1c] using (nb056_compact_fv_empty_0050)

theorem nb056_compact_fv_empty_0051 (f : Var) : (nb056_alpha_dummy_052 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0143 (f : Var) : (nb056_alpha_dummy_052 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_052, fv_syn_c1c] using (nb056_compact_fv_empty_0051 f)

theorem nb056_compact_fv_empty_0052 : (nb056_alpha_dummy_049) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0144 : (nb056_alpha_dummy_049) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_049, fv_syn_c1c] using (nb056_compact_fv_empty_0052)

theorem nb056_compact_fv_empty_0053 (f : Var) : (nb056_alpha_dummy_051 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0145 (f : Var) : (nb056_alpha_dummy_051 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_051, fv_syn_c1c] using (nb056_compact_fv_empty_0053 f)

theorem nb056_compact_fv_empty_0054 : (nb056_alpha_dummy_055) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0146 : (nb056_alpha_dummy_055) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_055, fv_syn_c1c] using (nb056_compact_fv_empty_0054)

theorem nb056_compact_fv_empty_0055 (f : Var) : (nb056_alpha_dummy_056 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0147 (f : Var) : (nb056_alpha_dummy_056 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_056, fv_syn_c1c] using (nb056_compact_fv_empty_0055 f)

theorem nb056_compact_fv_empty_0056 : (nb056_alpha_dummy_053) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0148 : (nb056_alpha_dummy_053) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_053, fv_syn_c1c] using (nb056_compact_fv_empty_0056)

theorem nb056_compact_fv_empty_0057 (f : Var) : (nb056_alpha_dummy_054 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0149 (f : Var) : (nb056_alpha_dummy_054 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_054, fv_syn_c1c] using (nb056_compact_fv_empty_0057 f)

theorem nb056_compact_fv_empty_0058 : (nb056_alpha_dummy_007) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0150 : (nb056_alpha_dummy_007) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_007, fv_syn_c1c] using (nb056_compact_fv_empty_0058)

theorem nb056_compact_fv_empty_0059 (f : Var) : (nb056_alpha_dummy_010 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0151 (f : Var) : (nb056_alpha_dummy_010 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_010, fv_syn_c1c] using (nb056_compact_fv_empty_0059 f)

theorem nb056_compact_envfresh_0007 (f : Var) : TEnvFresh [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_065) (nb056_alpha_dummy_068 f) (nb056_wpp_notmem_0130) (nb056_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb056_alpha_dummy_064) (nb056_alpha_dummy_067 f) (nb056_wpp_notmem_0132) (nb056_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb056_alpha_dummy_063) (nb056_alpha_dummy_066 f) (nb056_wpp_notmem_0134) (nb056_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb056_alpha_dummy_061) (nb056_alpha_dummy_062 f) (nb056_wpp_notmem_0136) (nb056_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb056_alpha_dummy_057) (nb056_alpha_dummy_059 f) (nb056_wpp_notmem_0138) (nb056_wpp_notmem_0139 f) (TEnvFresh.consFresh (nb056_alpha_dummy_058) (nb056_alpha_dummy_060 f) (nb056_wpp_notmem_0140) (nb056_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb056_alpha_dummy_050) (nb056_alpha_dummy_052 f) (nb056_wpp_notmem_0142) (nb056_wpp_notmem_0143 f) (TEnvFresh.consFresh (nb056_alpha_dummy_049) (nb056_alpha_dummy_051 f) (nb056_wpp_notmem_0144) (nb056_wpp_notmem_0145 f) (TEnvFresh.consFresh (nb056_alpha_dummy_055) (nb056_alpha_dummy_056 f) (nb056_wpp_notmem_0146) (nb056_wpp_notmem_0147 f) (TEnvFresh.consFresh (nb056_alpha_dummy_053) (nb056_alpha_dummy_054 f) (nb056_wpp_notmem_0148) (nb056_wpp_notmem_0149 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0150) (nb056_wpp_notmem_0151 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0020) (nb056_wpp_notmem_0021 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0022) (nb056_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0024) (nb056_wpp_notmem_0025 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0026) (nb056_wpp_notmem_0027 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0028) (nb056_wpp_notmem_0029 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0030) (nb056_wpp_notmem_0031 f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb056_wpp_refl_0007 (f : Var) : TReflOn [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0007 f)

theorem nb056_wpp_notmem_0152 : (nb056_alpha_dummy_065) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_065, fv_syn_c0] using (nb056_compact_fv_empty_0038)

theorem nb056_wpp_notmem_0153 (f : Var) : (nb056_alpha_dummy_068 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_068, fv_syn_c0] using (nb056_compact_fv_empty_0039 f)

theorem nb056_wpp_notmem_0154 : (nb056_alpha_dummy_064) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_064, fv_syn_c0] using (nb056_compact_fv_empty_0040)

theorem nb056_wpp_notmem_0155 (f : Var) : (nb056_alpha_dummy_067 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_067, fv_syn_c0] using (nb056_compact_fv_empty_0041 f)

theorem nb056_wpp_notmem_0156 : (nb056_alpha_dummy_063) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_063, fv_syn_c0] using (nb056_compact_fv_empty_0042)

theorem nb056_wpp_notmem_0157 (f : Var) : (nb056_alpha_dummy_066 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_066, fv_syn_c0] using (nb056_compact_fv_empty_0043 f)

theorem nb056_wpp_notmem_0158 : (nb056_alpha_dummy_061) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_061, fv_syn_c0] using (nb056_compact_fv_empty_0044)

theorem nb056_wpp_notmem_0159 (f : Var) : (nb056_alpha_dummy_062 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_062, fv_syn_c0] using (nb056_compact_fv_empty_0045 f)

theorem nb056_wpp_notmem_0160 : (nb056_alpha_dummy_057) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_057, fv_syn_c0] using (nb056_compact_fv_empty_0046)

theorem nb056_wpp_notmem_0161 (f : Var) : (nb056_alpha_dummy_059 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_059, fv_syn_c0] using (nb056_compact_fv_empty_0047 f)

theorem nb056_wpp_notmem_0162 : (nb056_alpha_dummy_058) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_058, fv_syn_c0] using (nb056_compact_fv_empty_0048)

theorem nb056_wpp_notmem_0163 (f : Var) : (nb056_alpha_dummy_060 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_060, fv_syn_c0] using (nb056_compact_fv_empty_0049 f)

theorem nb056_wpp_notmem_0164 : (nb056_alpha_dummy_050) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_050, fv_syn_c0] using (nb056_compact_fv_empty_0050)

theorem nb056_wpp_notmem_0165 (f : Var) : (nb056_alpha_dummy_052 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_052, fv_syn_c0] using (nb056_compact_fv_empty_0051 f)

theorem nb056_wpp_notmem_0166 : (nb056_alpha_dummy_049) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_049, fv_syn_c0] using (nb056_compact_fv_empty_0052)

theorem nb056_wpp_notmem_0167 (f : Var) : (nb056_alpha_dummy_051 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_051, fv_syn_c0] using (nb056_compact_fv_empty_0053 f)

theorem nb056_wpp_notmem_0168 : (nb056_alpha_dummy_055) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_055, fv_syn_c0] using (nb056_compact_fv_empty_0054)

theorem nb056_wpp_notmem_0169 (f : Var) : (nb056_alpha_dummy_056 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_056, fv_syn_c0] using (nb056_compact_fv_empty_0055 f)

theorem nb056_wpp_notmem_0170 : (nb056_alpha_dummy_053) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_053, fv_syn_c0] using (nb056_compact_fv_empty_0056)

theorem nb056_wpp_notmem_0171 (f : Var) : (nb056_alpha_dummy_054 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_054, fv_syn_c0] using (nb056_compact_fv_empty_0057 f)

theorem nb056_wpp_notmem_0172 : (nb056_alpha_dummy_007) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_007, fv_syn_c0] using (nb056_compact_fv_empty_0058)

theorem nb056_wpp_notmem_0173 (f : Var) : (nb056_alpha_dummy_010 f) ∉ ((syn_c0)).fv := by
  simpa only [nb056_alpha_dummy_010, fv_syn_c0] using (nb056_compact_fv_empty_0059 f)

theorem nb056_compact_envfresh_0008 (f : Var) : TEnvFresh [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_065) (nb056_alpha_dummy_068 f) (nb056_wpp_notmem_0152) (nb056_wpp_notmem_0153 f) (TEnvFresh.consFresh (nb056_alpha_dummy_064) (nb056_alpha_dummy_067 f) (nb056_wpp_notmem_0154) (nb056_wpp_notmem_0155 f) (TEnvFresh.consFresh (nb056_alpha_dummy_063) (nb056_alpha_dummy_066 f) (nb056_wpp_notmem_0156) (nb056_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb056_alpha_dummy_061) (nb056_alpha_dummy_062 f) (nb056_wpp_notmem_0158) (nb056_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb056_alpha_dummy_057) (nb056_alpha_dummy_059 f) (nb056_wpp_notmem_0160) (nb056_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb056_alpha_dummy_058) (nb056_alpha_dummy_060 f) (nb056_wpp_notmem_0162) (nb056_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb056_alpha_dummy_050) (nb056_alpha_dummy_052 f) (nb056_wpp_notmem_0164) (nb056_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb056_alpha_dummy_049) (nb056_alpha_dummy_051 f) (nb056_wpp_notmem_0166) (nb056_wpp_notmem_0167 f) (TEnvFresh.consFresh (nb056_alpha_dummy_055) (nb056_alpha_dummy_056 f) (nb056_wpp_notmem_0168) (nb056_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb056_alpha_dummy_053) (nb056_alpha_dummy_054 f) (nb056_wpp_notmem_0170) (nb056_wpp_notmem_0171 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0172) (nb056_wpp_notmem_0173 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0052) (nb056_wpp_notmem_0053 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0054) (nb056_wpp_notmem_0055 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0056) (nb056_wpp_notmem_0057 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0058) (nb056_wpp_notmem_0059 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0060) (nb056_wpp_notmem_0061 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0062) (nb056_wpp_notmem_0063 f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb056_wpp_refl_0008 (f : Var) : TReflOn [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0008 f)

noncomputable def nb056_split_alpha_0005 (f : Var) : TAlphaWff [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_063)) (syn_cun (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_066 f)) (syn_cun (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c0) (nb056_wpp_refl_0008 f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb056_wpp_notmem_0174 : (nb056_alpha_dummy_061) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_061, fv_syn_cnnc] using (nb056_compact_fv_empty_0044)

theorem nb056_wpp_notmem_0175 (f : Var) : (nb056_alpha_dummy_062 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_062, fv_syn_cnnc] using (nb056_compact_fv_empty_0045 f)

theorem nb056_wpp_notmem_0176 : (nb056_alpha_dummy_057) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_057, fv_syn_cnnc] using (nb056_compact_fv_empty_0046)

theorem nb056_wpp_notmem_0177 (f : Var) : (nb056_alpha_dummy_059 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_059, fv_syn_cnnc] using (nb056_compact_fv_empty_0047 f)

theorem nb056_wpp_notmem_0178 : (nb056_alpha_dummy_058) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_058, fv_syn_cnnc] using (nb056_compact_fv_empty_0048)

theorem nb056_wpp_notmem_0179 (f : Var) : (nb056_alpha_dummy_060 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_060, fv_syn_cnnc] using (nb056_compact_fv_empty_0049 f)

theorem nb056_wpp_notmem_0180 : (nb056_alpha_dummy_050) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_050, fv_syn_cnnc] using (nb056_compact_fv_empty_0050)

theorem nb056_wpp_notmem_0181 (f : Var) : (nb056_alpha_dummy_052 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_052, fv_syn_cnnc] using (nb056_compact_fv_empty_0051 f)

theorem nb056_wpp_notmem_0182 : (nb056_alpha_dummy_049) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_049, fv_syn_cnnc] using (nb056_compact_fv_empty_0052)

theorem nb056_wpp_notmem_0183 (f : Var) : (nb056_alpha_dummy_051 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_051, fv_syn_cnnc] using (nb056_compact_fv_empty_0053 f)

theorem nb056_wpp_notmem_0184 : (nb056_alpha_dummy_055) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_055, fv_syn_cnnc] using (nb056_compact_fv_empty_0054)

theorem nb056_wpp_notmem_0185 (f : Var) : (nb056_alpha_dummy_056 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_056, fv_syn_cnnc] using (nb056_compact_fv_empty_0055 f)

theorem nb056_wpp_notmem_0186 : (nb056_alpha_dummy_053) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_053, fv_syn_cnnc] using (nb056_compact_fv_empty_0056)

theorem nb056_wpp_notmem_0187 (f : Var) : (nb056_alpha_dummy_054 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_054, fv_syn_cnnc] using (nb056_compact_fv_empty_0057 f)

theorem nb056_wpp_notmem_0188 : (nb056_alpha_dummy_007) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_007, fv_syn_cnnc] using (nb056_compact_fv_empty_0058)

theorem nb056_wpp_notmem_0189 (f : Var) : (nb056_alpha_dummy_010 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb056_alpha_dummy_010, fv_syn_cnnc] using (nb056_compact_fv_empty_0059 f)

theorem nb056_compact_envfresh_0009 (f : Var) : TEnvFresh [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb056_alpha_dummy_061) (nb056_alpha_dummy_062 f) (nb056_wpp_notmem_0174) (nb056_wpp_notmem_0175 f) (TEnvFresh.consFresh (nb056_alpha_dummy_057) (nb056_alpha_dummy_059 f) (nb056_wpp_notmem_0176) (nb056_wpp_notmem_0177 f) (TEnvFresh.consFresh (nb056_alpha_dummy_058) (nb056_alpha_dummy_060 f) (nb056_wpp_notmem_0178) (nb056_wpp_notmem_0179 f) (TEnvFresh.consFresh (nb056_alpha_dummy_050) (nb056_alpha_dummy_052 f) (nb056_wpp_notmem_0180) (nb056_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb056_alpha_dummy_049) (nb056_alpha_dummy_051 f) (nb056_wpp_notmem_0182) (nb056_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb056_alpha_dummy_055) (nb056_alpha_dummy_056 f) (nb056_wpp_notmem_0184) (nb056_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb056_alpha_dummy_053) (nb056_alpha_dummy_054 f) (nb056_wpp_notmem_0186) (nb056_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb056_alpha_dummy_007) (nb056_alpha_dummy_010 f) (nb056_wpp_notmem_0188) (nb056_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb056_alpha_dummy_006) (nb056_alpha_dummy_009 f) (nb056_wpp_notmem_0078) (nb056_wpp_notmem_0079 f) (TEnvFresh.consFresh (nb056_alpha_dummy_005) (nb056_alpha_dummy_008 f) (nb056_wpp_notmem_0080) (nb056_wpp_notmem_0081 f) (TEnvFresh.consFresh (nb056_alpha_dummy_011) (nb056_alpha_dummy_012 f) (nb056_wpp_notmem_0082) (nb056_wpp_notmem_0083 f) (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f) (nb056_wpp_notmem_0084) (nb056_wpp_notmem_0085 f) (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f) (nb056_wpp_notmem_0086) (nb056_wpp_notmem_0087 f) (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0088) (nb056_wpp_notmem_0089 f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb056_wpp_refl_0009 (f : Var) : TReflOn [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0009 f)

noncomputable def nb056_split_alpha_0006 (f : Var) : TAlphaWff [((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (Wff.classEq (Class.cv (nb056_alpha_dummy_049)) (syn_cphi (Class.cv (nb056_alpha_dummy_050)))) (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f)) (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_050))).fv) (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_052 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0053 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0053 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)), ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)), ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)), ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_c1c) (nb056_wpp_refl_0007 f))) (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0005 f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0009 f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)), ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)), ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)), ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)), ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)), ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)), ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)), ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)), ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)), ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)), ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)), ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)), ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)] (syn_cnnc) (nb056_wpp_refl_0009 f))))))))))))))))))

theorem nb056_compact_fv_empty_0060 : (nb056_alpha_dummy_083) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0190 : (nb056_alpha_dummy_083) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_083, fv_syn_c1c] using (nb056_compact_fv_empty_0060)

theorem nb056_compact_fv_empty_0061 (f : Var) : (nb056_alpha_dummy_084 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb056_wpp_notmem_0191 (f : Var) : (nb056_alpha_dummy_084 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb056_alpha_dummy_084, fv_syn_c1c] using (nb056_compact_fv_empty_0061 f)

theorem nb056_compact_fv_empty_0062 : (nb056_alpha_dummy_081) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
