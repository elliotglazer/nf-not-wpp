import NAR4C055C001Part006

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

noncomputable def nb055_split_alpha_0003 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)), ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)), ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)), ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (Class.cv (nb055_alpha_dummy_015))) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_023)) (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc)) (syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c)) (Class.cv (nb055_alpha_dummy_022)))))) (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (Class.cv (nb055_alpha_dummy_017 x y))) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_025 x y)) (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc)) (syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c)) (Class.cv (nb055_alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0059 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0057 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_015))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0024) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0025 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0024) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0025 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_030), (nb055_alpha_dummy_033 x y)), ((nb055_alpha_dummy_029), (nb055_alpha_dummy_032 x y)), ((nb055_alpha_dummy_028), (nb055_alpha_dummy_031 x y)), ((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)), ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)), ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)), ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)), ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c1c) (nb055_wpp_refl_0003 x y))) (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0002 x y)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)), ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)), ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)), ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)), ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0005 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)), ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)), ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)), ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)), ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0005 x y))))))))))))

theorem nb055_wpp_notmem_0120 : (nb055_alpha_dummy_046) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0038)

theorem nb055_wpp_notmem_0121 (x : Var) (y : Var) : (nb055_alpha_dummy_047 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_047, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0039 x y)

theorem nb055_wpp_notmem_0122 : (nb055_alpha_dummy_015) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_015, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0012)

theorem nb055_wpp_notmem_0123 (x : Var) (y : Var) : (nb055_alpha_dummy_017 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_017, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0013 x y)

theorem nb055_wpp_notmem_0124 : (nb055_alpha_dummy_014) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_014, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0014)

theorem nb055_wpp_notmem_0125 (x : Var) (y : Var) : (nb055_alpha_dummy_016 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_016, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0015 x y)

theorem nb055_wpp_notmem_0126 : (nb055_alpha_dummy_044) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0040)

theorem nb055_wpp_notmem_0127 (x : Var) (y : Var) : (nb055_alpha_dummy_045 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0041 x y)

theorem nb055_wpp_notmem_0128 : (nb055_alpha_dummy_018) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_018, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0018)

theorem nb055_wpp_notmem_0129 (x : Var) (y : Var) : (nb055_alpha_dummy_019 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_019, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0019 x y)

theorem nb055_wpp_notmem_0130 : (nb055_alpha_dummy_007) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_007, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0020)

theorem nb055_wpp_notmem_0131 (x : Var) (y : Var) : (nb055_alpha_dummy_009 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_009, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0021 x y)

theorem nb055_wpp_notmem_0132 : (nb055_alpha_dummy_006) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0022)

theorem nb055_wpp_notmem_0133 (x : Var) (y : Var) : (nb055_alpha_dummy_008 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_008, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0023 x y)

theorem nb055_wpp_notmem_0134 : (nb055_alpha_dummy_012) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_012, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0024)

theorem nb055_wpp_notmem_0135 (x : Var) (y : Var) : (nb055_alpha_dummy_013 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_013, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0025 x y)

theorem nb055_wpp_notmem_0136 : (nb055_alpha_dummy_010) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_010, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0026)

theorem nb055_wpp_notmem_0137 (x : Var) (y : Var) : (nb055_alpha_dummy_011 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_011, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0027 x y)

theorem nb055_wpp_notmem_0138 : (nb055_alpha_dummy_002) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0028)

theorem nb055_wpp_notmem_0139 (x : Var) (y : Var) : (nb055_alpha_dummy_003 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0029 x y)

theorem nb055_wpp_notmem_0140 : (nb055_alpha_dummy_001) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0030)

theorem nb055_wpp_notmem_0141 (y : Var) : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0031 y)

theorem nb055_wpp_notmem_0142 : (nb055_alpha_dummy_000) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_000, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0032)

theorem nb055_wpp_notmem_0143 (x : Var) : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0033 x)

theorem nb055_wpp_notmem_0144 : (nb055_alpha_dummy_004) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0034)

theorem nb055_wpp_notmem_0145 (x : Var) (y : Var) : (nb055_alpha_dummy_005 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb055_alpha_dummy_005, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb055_compact_fv_empty_0035 x y)

theorem nb055_compact_envfresh_0006 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_046) (nb055_alpha_dummy_047 x y) (nb055_wpp_notmem_0120) (nb055_wpp_notmem_0121 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_015) (nb055_alpha_dummy_017 x y) (nb055_wpp_notmem_0122) (nb055_wpp_notmem_0123 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_014) (nb055_alpha_dummy_016 x y) (nb055_wpp_notmem_0124) (nb055_wpp_notmem_0125 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_044) (nb055_alpha_dummy_045 x y) (nb055_wpp_notmem_0126) (nb055_wpp_notmem_0127 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_018) (nb055_alpha_dummy_019 x y) (nb055_wpp_notmem_0128) (nb055_wpp_notmem_0129 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_007) (nb055_alpha_dummy_009 x y) (nb055_wpp_notmem_0130) (nb055_wpp_notmem_0131 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_006) (nb055_alpha_dummy_008 x y) (nb055_wpp_notmem_0132) (nb055_wpp_notmem_0133 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_012) (nb055_alpha_dummy_013 x y) (nb055_wpp_notmem_0134) (nb055_wpp_notmem_0135 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_010) (nb055_alpha_dummy_011 x y) (nb055_wpp_notmem_0136) (nb055_wpp_notmem_0137 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0138) (nb055_wpp_notmem_0139 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0140) (nb055_wpp_notmem_0141 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0142) (nb055_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0144) (nb055_wpp_notmem_0145 x y) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))

noncomputable def nb055_wpp_refl_0006 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0006 x y)

noncomputable def nb055_split_alpha_0004 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_044)) (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_044)) (Class.cab (nb055_alpha_dummy_014) (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001)) (Wff.classEq (Class.cv (nb055_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_045 x y)) (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_045 x y)) (Class.cab (nb055_alpha_dummy_016 x y) (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0055 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0051) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0053 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0049 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0045) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0047 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0042) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0043 x y) 0)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0003 x y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0003 x y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_ccompl (syn_csn (syn_c0c))) (nb055_wpp_refl_0006 x y))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0055 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0051) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0053 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0049 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0045) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0047 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0042) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0043 x y) 0)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0003 x y))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0003 x y))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)), ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)), ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_ccompl (syn_csn (syn_c0c))) (nb055_wpp_refl_0006 x y)))))))))))))))))))

theorem nb055_compact_fv_empty_0042 : (nb055_alpha_dummy_058) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0146 : (nb055_alpha_dummy_058) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_058, fv_syn_c1c] using (nb055_compact_fv_empty_0042)

theorem nb055_compact_fv_empty_0043 (x : Var) (y : Var) : (nb055_alpha_dummy_061 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0147 (x : Var) (y : Var) : (nb055_alpha_dummy_061 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_061, fv_syn_c1c] using (nb055_compact_fv_empty_0043 x y)

theorem nb055_compact_fv_empty_0044 : (nb055_alpha_dummy_057) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0148 : (nb055_alpha_dummy_057) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_057, fv_syn_c1c] using (nb055_compact_fv_empty_0044)

theorem nb055_compact_fv_empty_0045 (x : Var) (y : Var) : (nb055_alpha_dummy_060 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0149 (x : Var) (y : Var) : (nb055_alpha_dummy_060 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_060, fv_syn_c1c] using (nb055_compact_fv_empty_0045 x y)

theorem nb055_compact_fv_empty_0046 : (nb055_alpha_dummy_056) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0150 : (nb055_alpha_dummy_056) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_056, fv_syn_c1c] using (nb055_compact_fv_empty_0046)

theorem nb055_compact_fv_empty_0047 (x : Var) (y : Var) : (nb055_alpha_dummy_059 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0151 (x : Var) (y : Var) : (nb055_alpha_dummy_059 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_059, fv_syn_c1c] using (nb055_compact_fv_empty_0047 x y)

theorem nb055_compact_fv_empty_0048 : (nb055_alpha_dummy_054) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0152 : (nb055_alpha_dummy_054) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_054, fv_syn_c1c] using (nb055_compact_fv_empty_0048)

theorem nb055_compact_fv_empty_0049 (x : Var) (y : Var) : (nb055_alpha_dummy_055 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0153 (x : Var) (y : Var) : (nb055_alpha_dummy_055 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_055, fv_syn_c1c] using (nb055_compact_fv_empty_0049 x y)

theorem nb055_compact_fv_empty_0050 : (nb055_alpha_dummy_050) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0154 : (nb055_alpha_dummy_050) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_050, fv_syn_c1c] using (nb055_compact_fv_empty_0050)

theorem nb055_compact_fv_empty_0051 (x : Var) (y : Var) : (nb055_alpha_dummy_052 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0155 (x : Var) (y : Var) : (nb055_alpha_dummy_052 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_052, fv_syn_c1c] using (nb055_compact_fv_empty_0051 x y)

theorem nb055_compact_fv_empty_0052 : (nb055_alpha_dummy_051) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0156 : (nb055_alpha_dummy_051) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_051, fv_syn_c1c] using (nb055_compact_fv_empty_0052)

theorem nb055_compact_fv_empty_0053 (x : Var) (y : Var) : (nb055_alpha_dummy_053 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0157 (x : Var) (y : Var) : (nb055_alpha_dummy_053 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_053, fv_syn_c1c] using (nb055_compact_fv_empty_0053 x y)

theorem nb055_compact_envfresh_0007 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_058) (nb055_alpha_dummy_061 x y) (nb055_wpp_notmem_0146) (nb055_wpp_notmem_0147 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_057) (nb055_alpha_dummy_060 x y) (nb055_wpp_notmem_0148) (nb055_wpp_notmem_0149 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_056) (nb055_alpha_dummy_059 x y) (nb055_wpp_notmem_0150) (nb055_wpp_notmem_0151 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_054) (nb055_alpha_dummy_055 x y) (nb055_wpp_notmem_0152) (nb055_wpp_notmem_0153 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_050) (nb055_alpha_dummy_052 x y) (nb055_wpp_notmem_0154) (nb055_wpp_notmem_0155 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_051) (nb055_alpha_dummy_053 x y) (nb055_wpp_notmem_0156) (nb055_wpp_notmem_0157 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_007) (nb055_alpha_dummy_009 x y) (nb055_wpp_notmem_0020) (nb055_wpp_notmem_0021 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_006) (nb055_alpha_dummy_008 x y) (nb055_wpp_notmem_0022) (nb055_wpp_notmem_0023 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_012) (nb055_alpha_dummy_013 x y) (nb055_wpp_notmem_0024) (nb055_wpp_notmem_0025 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_010) (nb055_alpha_dummy_011 x y) (nb055_wpp_notmem_0026) (nb055_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0028) (nb055_wpp_notmem_0029 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0030) (nb055_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0032) (nb055_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0034) (nb055_wpp_notmem_0035 x y) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))

noncomputable def nb055_wpp_refl_0007 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0007 x y)

theorem nb055_wpp_notmem_0158 : (nb055_alpha_dummy_058) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_058, fv_syn_c0] using (nb055_compact_fv_empty_0042)

theorem nb055_wpp_notmem_0159 (x : Var) (y : Var) : (nb055_alpha_dummy_061 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_061, fv_syn_c0] using (nb055_compact_fv_empty_0043 x y)

theorem nb055_wpp_notmem_0160 : (nb055_alpha_dummy_057) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_057, fv_syn_c0] using (nb055_compact_fv_empty_0044)

theorem nb055_wpp_notmem_0161 (x : Var) (y : Var) : (nb055_alpha_dummy_060 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_060, fv_syn_c0] using (nb055_compact_fv_empty_0045 x y)

theorem nb055_wpp_notmem_0162 : (nb055_alpha_dummy_056) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_056, fv_syn_c0] using (nb055_compact_fv_empty_0046)

theorem nb055_wpp_notmem_0163 (x : Var) (y : Var) : (nb055_alpha_dummy_059 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_059, fv_syn_c0] using (nb055_compact_fv_empty_0047 x y)

theorem nb055_wpp_notmem_0164 : (nb055_alpha_dummy_054) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_054, fv_syn_c0] using (nb055_compact_fv_empty_0048)

theorem nb055_wpp_notmem_0165 (x : Var) (y : Var) : (nb055_alpha_dummy_055 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_055, fv_syn_c0] using (nb055_compact_fv_empty_0049 x y)

theorem nb055_wpp_notmem_0166 : (nb055_alpha_dummy_050) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_050, fv_syn_c0] using (nb055_compact_fv_empty_0050)

theorem nb055_wpp_notmem_0167 (x : Var) (y : Var) : (nb055_alpha_dummy_052 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_052, fv_syn_c0] using (nb055_compact_fv_empty_0051 x y)

theorem nb055_wpp_notmem_0168 : (nb055_alpha_dummy_051) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_051, fv_syn_c0] using (nb055_compact_fv_empty_0052)

theorem nb055_wpp_notmem_0169 (x : Var) (y : Var) : (nb055_alpha_dummy_053 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb055_alpha_dummy_053, fv_syn_c0] using (nb055_compact_fv_empty_0053 x y)

theorem nb055_compact_envfresh_0008 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_058) (nb055_alpha_dummy_061 x y) (nb055_wpp_notmem_0158) (nb055_wpp_notmem_0159 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_057) (nb055_alpha_dummy_060 x y) (nb055_wpp_notmem_0160) (nb055_wpp_notmem_0161 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_056) (nb055_alpha_dummy_059 x y) (nb055_wpp_notmem_0162) (nb055_wpp_notmem_0163 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_054) (nb055_alpha_dummy_055 x y) (nb055_wpp_notmem_0164) (nb055_wpp_notmem_0165 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_050) (nb055_alpha_dummy_052 x y) (nb055_wpp_notmem_0166) (nb055_wpp_notmem_0167 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_051) (nb055_alpha_dummy_053 x y) (nb055_wpp_notmem_0168) (nb055_wpp_notmem_0169 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_007) (nb055_alpha_dummy_009 x y) (nb055_wpp_notmem_0056) (nb055_wpp_notmem_0057 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_006) (nb055_alpha_dummy_008 x y) (nb055_wpp_notmem_0058) (nb055_wpp_notmem_0059 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_012) (nb055_alpha_dummy_013 x y) (nb055_wpp_notmem_0060) (nb055_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_010) (nb055_alpha_dummy_011 x y) (nb055_wpp_notmem_0062) (nb055_wpp_notmem_0063 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0064) (nb055_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0066) (nb055_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0068) (nb055_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0070) (nb055_wpp_notmem_0071 x y) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))

noncomputable def nb055_wpp_refl_0008 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0008 x y)

noncomputable def nb055_split_alpha_0005 (x : Var) (y : Var) : TAlphaWff [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_056)) (syn_cun (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_059 x y)) (syn_cun (Class.cv (nb055_alpha_dummy_060 x y)) (Class.cv (nb055_alpha_dummy_061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c0) (nb055_wpp_refl_0008 x y))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb055_wpp_notmem_0170 : (nb055_alpha_dummy_054) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_054, fv_syn_cnnc] using (nb055_compact_fv_empty_0048)

theorem nb055_wpp_notmem_0171 (x : Var) (y : Var) : (nb055_alpha_dummy_055 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_055, fv_syn_cnnc] using (nb055_compact_fv_empty_0049 x y)

theorem nb055_wpp_notmem_0172 : (nb055_alpha_dummy_050) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_050, fv_syn_cnnc] using (nb055_compact_fv_empty_0050)

theorem nb055_wpp_notmem_0173 (x : Var) (y : Var) : (nb055_alpha_dummy_052 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_052, fv_syn_cnnc] using (nb055_compact_fv_empty_0051 x y)

theorem nb055_wpp_notmem_0174 : (nb055_alpha_dummy_051) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_051, fv_syn_cnnc] using (nb055_compact_fv_empty_0052)

theorem nb055_wpp_notmem_0175 (x : Var) (y : Var) : (nb055_alpha_dummy_053 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb055_alpha_dummy_053, fv_syn_cnnc] using (nb055_compact_fv_empty_0053 x y)

theorem nb055_compact_envfresh_0009 (x : Var) (y : Var) : TEnvFresh [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb055_alpha_dummy_054) (nb055_alpha_dummy_055 x y) (nb055_wpp_notmem_0170) (nb055_wpp_notmem_0171 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_050) (nb055_alpha_dummy_052 x y) (nb055_wpp_notmem_0172) (nb055_wpp_notmem_0173 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_051) (nb055_alpha_dummy_053 x y) (nb055_wpp_notmem_0174) (nb055_wpp_notmem_0175 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_007) (nb055_alpha_dummy_009 x y) (nb055_wpp_notmem_0086) (nb055_wpp_notmem_0087 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_006) (nb055_alpha_dummy_008 x y) (nb055_wpp_notmem_0088) (nb055_wpp_notmem_0089 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_012) (nb055_alpha_dummy_013 x y) (nb055_wpp_notmem_0090) (nb055_wpp_notmem_0091 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_010) (nb055_alpha_dummy_011 x y) (nb055_wpp_notmem_0092) (nb055_wpp_notmem_0093 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_002) (nb055_alpha_dummy_003 x y) (nb055_wpp_notmem_0094) (nb055_wpp_notmem_0095 x y) (TEnvFresh.consFresh (nb055_alpha_dummy_001) y (nb055_wpp_notmem_0096) (nb055_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb055_alpha_dummy_000) x (nb055_wpp_notmem_0098) (nb055_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb055_alpha_dummy_004) (nb055_alpha_dummy_005 x y) (nb055_wpp_notmem_0100) (nb055_wpp_notmem_0101 x y) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))

noncomputable def nb055_wpp_refl_0009 (x : Var) (y : Var) : TReflOn [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb055_compact_envfresh_0009 x y)

noncomputable def nb055_split_alpha_0006 (x : Var) (y : Var) (dv_x_y : x ≠ y) : TAlphaWff [((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_007)) (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_006)) (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))) (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_009 x y)) (syn_cop (Class.cv x) (Class.cv y))) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0015) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0017 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0013 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0009) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0011 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0006) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0007 x y) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.neg (nb055_split_alpha_0001 x y))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0018) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0019 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0015) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0017 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0012) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0013 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0009) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0011 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0006) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0007 x y) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.neg (nb055_split_alpha_0001 x y))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0004 x y))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))).fv ∪ ((Class.cv (nb055_alpha_dummy_002))).fv) (by decide)) (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb055_alpha_dummy_003 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_007))).fv) (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_009 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0064) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0065 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)), ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_c1c) (nb055_wpp_refl_0007 x y))) (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0005 x y)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0009 x y))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)), ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)), ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))] (syn_cnnc) (nb055_wpp_refl_0009 x y))))))))))))))))))))

theorem nb055_compact_fv_empty_0054 : (nb055_alpha_dummy_076) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0176 : (nb055_alpha_dummy_076) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_076, fv_syn_c1c] using (nb055_compact_fv_empty_0054)

theorem nb055_compact_fv_empty_0055 (x : Var) (y : Var) : (nb055_alpha_dummy_077 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0177 (x : Var) (y : Var) : (nb055_alpha_dummy_077 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_077, fv_syn_c1c] using (nb055_compact_fv_empty_0055 x y)

theorem nb055_compact_fv_empty_0056 : (nb055_alpha_dummy_074) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0178 : (nb055_alpha_dummy_074) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_074, fv_syn_c1c] using (nb055_compact_fv_empty_0056)

theorem nb055_compact_fv_empty_0057 (x : Var) (y : Var) : (nb055_alpha_dummy_075 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0179 (x : Var) (y : Var) : (nb055_alpha_dummy_075 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_075, fv_syn_c1c] using (nb055_compact_fv_empty_0057 x y)

theorem nb055_compact_fv_empty_0058 : (nb055_alpha_dummy_072) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0180 : (nb055_alpha_dummy_072) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_072, fv_syn_c1c] using (nb055_compact_fv_empty_0058)

theorem nb055_compact_fv_empty_0059 (x : Var) (y : Var) : (nb055_alpha_dummy_073 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb055_wpp_notmem_0181 (x : Var) (y : Var) : (nb055_alpha_dummy_073 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb055_alpha_dummy_073, fv_syn_c1c] using (nb055_compact_fv_empty_0059 x y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
