import NAR4C057C001Part009

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

noncomputable def nb057_wpp_refl_0012 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0012 f a)

noncomputable def nb057_split_alpha_0008 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (Class.cv (nb057_alpha_dummy_053))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_061)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_060)))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (Class.cv (nb057_alpha_dummy_055 f))) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_063 f)) (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c)) (Class.cv (nb057_alpha_dummy_062 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0083 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0081 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_053))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_055 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0056) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0057 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0057 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)), ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)), ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)), ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c1c) (nb057_wpp_refl_0010 f a))) (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0007 f a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0012 f a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)), ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)), ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)), ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)), ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_cnnc) (nb057_wpp_refl_0012 f a))))))))))))

theorem nb057_wpp_notmem_0208 : (nb057_alpha_dummy_084) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_084, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0064)

theorem nb057_wpp_notmem_0209 (f : Var) : (nb057_alpha_dummy_085 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_085, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0065 f)

theorem nb057_wpp_notmem_0210 : (nb057_alpha_dummy_053) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_053, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0044)

theorem nb057_wpp_notmem_0211 (f : Var) : (nb057_alpha_dummy_055 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_055, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0045 f)

theorem nb057_wpp_notmem_0212 : (nb057_alpha_dummy_052) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_052, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0046)

theorem nb057_wpp_notmem_0213 (f : Var) : (nb057_alpha_dummy_054 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_054, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0047 f)

theorem nb057_wpp_notmem_0214 : (nb057_alpha_dummy_082) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_082, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0066)

theorem nb057_wpp_notmem_0215 (f : Var) : (nb057_alpha_dummy_083 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_083, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0067 f)

theorem nb057_wpp_notmem_0216 : (nb057_alpha_dummy_056) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_056, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0050)

theorem nb057_wpp_notmem_0217 (f : Var) : (nb057_alpha_dummy_057 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_057, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0051 f)

theorem nb057_wpp_notmem_0218 : (nb057_alpha_dummy_045) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0052)

theorem nb057_wpp_notmem_0219 (f : Var) : (nb057_alpha_dummy_048 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_048, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0053 f)

theorem nb057_wpp_notmem_0220 : (nb057_alpha_dummy_044) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0054)

theorem nb057_wpp_notmem_0221 (f : Var) : (nb057_alpha_dummy_047 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_047, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0055 f)

theorem nb057_wpp_notmem_0222 : (nb057_alpha_dummy_050) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_050, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0056)

theorem nb057_wpp_notmem_0223 (f : Var) : (nb057_alpha_dummy_051 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_051, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0057 f)

theorem nb057_wpp_notmem_0224 : (nb057_alpha_dummy_042) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_042, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0058)

theorem nb057_wpp_notmem_0225 (f : Var) : (nb057_alpha_dummy_043 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_043, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0059 f)

theorem nb057_wpp_notmem_0226 : (nb057_alpha_dummy_040) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_040, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0060)

theorem nb057_wpp_notmem_0227 (f : Var) : (nb057_alpha_dummy_041 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb057_alpha_dummy_041, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb057_compact_fv_empty_0061 f)

theorem nb057_compact_envfresh_0013 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_084) (nb057_alpha_dummy_085 f) (nb057_wpp_notmem_0208) (nb057_wpp_notmem_0209 f) (TEnvFresh.consFresh (nb057_alpha_dummy_053) (nb057_alpha_dummy_055 f) (nb057_wpp_notmem_0210) (nb057_wpp_notmem_0211 f) (TEnvFresh.consFresh (nb057_alpha_dummy_052) (nb057_alpha_dummy_054 f) (nb057_wpp_notmem_0212) (nb057_wpp_notmem_0213 f) (TEnvFresh.consFresh (nb057_alpha_dummy_082) (nb057_alpha_dummy_083 f) (nb057_wpp_notmem_0214) (nb057_wpp_notmem_0215 f) (TEnvFresh.consFresh (nb057_alpha_dummy_056) (nb057_alpha_dummy_057 f) (nb057_wpp_notmem_0216) (nb057_wpp_notmem_0217 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0218) (nb057_wpp_notmem_0219 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0220) (nb057_wpp_notmem_0221 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0222) (nb057_wpp_notmem_0223 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0224) (nb057_wpp_notmem_0225 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0226) (nb057_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0100) (nb057_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0102) (nb057_wpp_notmem_0103 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0104) (nb057_wpp_notmem_0105 f a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))

noncomputable def nb057_wpp_refl_0013 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0013 f a)

noncomputable def nb057_split_alpha_0009 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_082)) (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_082)) (Class.cab (nb057_alpha_dummy_052) (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045)) (Wff.classEq (Class.cv (nb057_alpha_dummy_052)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_083 f)) (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_083 f)) (Class.cab (nb057_alpha_dummy_054 f) (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0079 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0075) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0077 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0008 f a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0008 f a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0013 f a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0079 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0075) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0077 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0008 f a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0008 f a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)), ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)), ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)), ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)), ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (nb057_wpp_refl_0013 f a)))))))))))))))))))

theorem nb057_compact_fv_empty_0068 : (nb057_alpha_dummy_104) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0228 : (nb057_alpha_dummy_104) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_104, fv_syn_c1c] using (nb057_compact_fv_empty_0068)

theorem nb057_compact_fv_empty_0069 (f : Var) : (nb057_alpha_dummy_107 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0229 (f : Var) : (nb057_alpha_dummy_107 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_107, fv_syn_c1c] using (nb057_compact_fv_empty_0069 f)

theorem nb057_compact_fv_empty_0070 : (nb057_alpha_dummy_103) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0230 : (nb057_alpha_dummy_103) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_103, fv_syn_c1c] using (nb057_compact_fv_empty_0070)

theorem nb057_compact_fv_empty_0071 (f : Var) : (nb057_alpha_dummy_106 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0231 (f : Var) : (nb057_alpha_dummy_106 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_106, fv_syn_c1c] using (nb057_compact_fv_empty_0071 f)

theorem nb057_compact_fv_empty_0072 : (nb057_alpha_dummy_102) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0232 : (nb057_alpha_dummy_102) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_102, fv_syn_c1c] using (nb057_compact_fv_empty_0072)

theorem nb057_compact_fv_empty_0073 (f : Var) : (nb057_alpha_dummy_105 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0233 (f : Var) : (nb057_alpha_dummy_105 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_105, fv_syn_c1c] using (nb057_compact_fv_empty_0073 f)

theorem nb057_compact_fv_empty_0074 : (nb057_alpha_dummy_100) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0234 : (nb057_alpha_dummy_100) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_100, fv_syn_c1c] using (nb057_compact_fv_empty_0074)

theorem nb057_compact_fv_empty_0075 (f : Var) : (nb057_alpha_dummy_101 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0235 (f : Var) : (nb057_alpha_dummy_101 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_101, fv_syn_c1c] using (nb057_compact_fv_empty_0075 f)

theorem nb057_compact_fv_empty_0076 : (nb057_alpha_dummy_096) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0236 : (nb057_alpha_dummy_096) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_096, fv_syn_c1c] using (nb057_compact_fv_empty_0076)

theorem nb057_compact_fv_empty_0077 (f : Var) : (nb057_alpha_dummy_098 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0237 (f : Var) : (nb057_alpha_dummy_098 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_098, fv_syn_c1c] using (nb057_compact_fv_empty_0077 f)

theorem nb057_compact_fv_empty_0078 : (nb057_alpha_dummy_097) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0238 : (nb057_alpha_dummy_097) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_097, fv_syn_c1c] using (nb057_compact_fv_empty_0078)

theorem nb057_compact_fv_empty_0079 (f : Var) : (nb057_alpha_dummy_099 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0239 (f : Var) : (nb057_alpha_dummy_099 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_099, fv_syn_c1c] using (nb057_compact_fv_empty_0079 f)

theorem nb057_compact_fv_empty_0080 : (nb057_alpha_dummy_089) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0240 : (nb057_alpha_dummy_089) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_089, fv_syn_c1c] using (nb057_compact_fv_empty_0080)

theorem nb057_compact_fv_empty_0081 (f : Var) : (nb057_alpha_dummy_091 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0241 (f : Var) : (nb057_alpha_dummy_091 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_091, fv_syn_c1c] using (nb057_compact_fv_empty_0081 f)

theorem nb057_compact_fv_empty_0082 : (nb057_alpha_dummy_088) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0242 : (nb057_alpha_dummy_088) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_088, fv_syn_c1c] using (nb057_compact_fv_empty_0082)

theorem nb057_compact_fv_empty_0083 (f : Var) : (nb057_alpha_dummy_090 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0243 (f : Var) : (nb057_alpha_dummy_090 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_090, fv_syn_c1c] using (nb057_compact_fv_empty_0083 f)

theorem nb057_compact_fv_empty_0084 : (nb057_alpha_dummy_094) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0244 : (nb057_alpha_dummy_094) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_094, fv_syn_c1c] using (nb057_compact_fv_empty_0084)

theorem nb057_compact_fv_empty_0085 (f : Var) : (nb057_alpha_dummy_095 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0245 (f : Var) : (nb057_alpha_dummy_095 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_095, fv_syn_c1c] using (nb057_compact_fv_empty_0085 f)

theorem nb057_compact_fv_empty_0086 : (nb057_alpha_dummy_092) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0246 : (nb057_alpha_dummy_092) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_092, fv_syn_c1c] using (nb057_compact_fv_empty_0086)

theorem nb057_compact_fv_empty_0087 (f : Var) : (nb057_alpha_dummy_093 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0247 (f : Var) : (nb057_alpha_dummy_093 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_093, fv_syn_c1c] using (nb057_compact_fv_empty_0087 f)

theorem nb057_compact_fv_empty_0088 : (nb057_alpha_dummy_046) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0248 : (nb057_alpha_dummy_046) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_046, fv_syn_c1c] using (nb057_compact_fv_empty_0088)

theorem nb057_compact_fv_empty_0089 (f : Var) : (nb057_alpha_dummy_049 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb057_wpp_notmem_0249 (f : Var) : (nb057_alpha_dummy_049 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb057_alpha_dummy_049, fv_syn_c1c] using (nb057_compact_fv_empty_0089 f)

theorem nb057_compact_envfresh_0014 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_104) (nb057_alpha_dummy_107 f) (nb057_wpp_notmem_0228) (nb057_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb057_alpha_dummy_103) (nb057_alpha_dummy_106 f) (nb057_wpp_notmem_0230) (nb057_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb057_alpha_dummy_102) (nb057_alpha_dummy_105 f) (nb057_wpp_notmem_0232) (nb057_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb057_alpha_dummy_100) (nb057_alpha_dummy_101 f) (nb057_wpp_notmem_0234) (nb057_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb057_alpha_dummy_096) (nb057_alpha_dummy_098 f) (nb057_wpp_notmem_0236) (nb057_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb057_alpha_dummy_097) (nb057_alpha_dummy_099 f) (nb057_wpp_notmem_0238) (nb057_wpp_notmem_0239 f) (TEnvFresh.consFresh (nb057_alpha_dummy_089) (nb057_alpha_dummy_091 f) (nb057_wpp_notmem_0240) (nb057_wpp_notmem_0241 f) (TEnvFresh.consFresh (nb057_alpha_dummy_088) (nb057_alpha_dummy_090 f) (nb057_wpp_notmem_0242) (nb057_wpp_notmem_0243 f) (TEnvFresh.consFresh (nb057_alpha_dummy_094) (nb057_alpha_dummy_095 f) (nb057_wpp_notmem_0244) (nb057_wpp_notmem_0245 f) (TEnvFresh.consFresh (nb057_alpha_dummy_092) (nb057_alpha_dummy_093 f) (nb057_wpp_notmem_0246) (nb057_wpp_notmem_0247 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0248) (nb057_wpp_notmem_0249 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0126) (nb057_wpp_notmem_0127 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0128) (nb057_wpp_notmem_0129 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0130) (nb057_wpp_notmem_0131 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0132) (nb057_wpp_notmem_0133 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0134) (nb057_wpp_notmem_0135 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0020) (nb057_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0022) (nb057_wpp_notmem_0023 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0024) (nb057_wpp_notmem_0025 f a) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb057_wpp_refl_0014 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0014 f a)

theorem nb057_wpp_notmem_0250 : (nb057_alpha_dummy_104) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_104, fv_syn_c0] using (nb057_compact_fv_empty_0068)

theorem nb057_wpp_notmem_0251 (f : Var) : (nb057_alpha_dummy_107 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_107, fv_syn_c0] using (nb057_compact_fv_empty_0069 f)

theorem nb057_wpp_notmem_0252 : (nb057_alpha_dummy_103) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_103, fv_syn_c0] using (nb057_compact_fv_empty_0070)

theorem nb057_wpp_notmem_0253 (f : Var) : (nb057_alpha_dummy_106 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_106, fv_syn_c0] using (nb057_compact_fv_empty_0071 f)

theorem nb057_wpp_notmem_0254 : (nb057_alpha_dummy_102) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_102, fv_syn_c0] using (nb057_compact_fv_empty_0072)

theorem nb057_wpp_notmem_0255 (f : Var) : (nb057_alpha_dummy_105 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_105, fv_syn_c0] using (nb057_compact_fv_empty_0073 f)

theorem nb057_wpp_notmem_0256 : (nb057_alpha_dummy_100) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_100, fv_syn_c0] using (nb057_compact_fv_empty_0074)

theorem nb057_wpp_notmem_0257 (f : Var) : (nb057_alpha_dummy_101 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_101, fv_syn_c0] using (nb057_compact_fv_empty_0075 f)

theorem nb057_wpp_notmem_0258 : (nb057_alpha_dummy_096) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_096, fv_syn_c0] using (nb057_compact_fv_empty_0076)

theorem nb057_wpp_notmem_0259 (f : Var) : (nb057_alpha_dummy_098 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_098, fv_syn_c0] using (nb057_compact_fv_empty_0077 f)

theorem nb057_wpp_notmem_0260 : (nb057_alpha_dummy_097) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_097, fv_syn_c0] using (nb057_compact_fv_empty_0078)

theorem nb057_wpp_notmem_0261 (f : Var) : (nb057_alpha_dummy_099 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_099, fv_syn_c0] using (nb057_compact_fv_empty_0079 f)

theorem nb057_wpp_notmem_0262 : (nb057_alpha_dummy_089) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_089, fv_syn_c0] using (nb057_compact_fv_empty_0080)

theorem nb057_wpp_notmem_0263 (f : Var) : (nb057_alpha_dummy_091 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_091, fv_syn_c0] using (nb057_compact_fv_empty_0081 f)

theorem nb057_wpp_notmem_0264 : (nb057_alpha_dummy_088) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_088, fv_syn_c0] using (nb057_compact_fv_empty_0082)

theorem nb057_wpp_notmem_0265 (f : Var) : (nb057_alpha_dummy_090 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_090, fv_syn_c0] using (nb057_compact_fv_empty_0083 f)

theorem nb057_wpp_notmem_0266 : (nb057_alpha_dummy_094) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_094, fv_syn_c0] using (nb057_compact_fv_empty_0084)

theorem nb057_wpp_notmem_0267 (f : Var) : (nb057_alpha_dummy_095 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_095, fv_syn_c0] using (nb057_compact_fv_empty_0085 f)

theorem nb057_wpp_notmem_0268 : (nb057_alpha_dummy_092) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_092, fv_syn_c0] using (nb057_compact_fv_empty_0086)

theorem nb057_wpp_notmem_0269 (f : Var) : (nb057_alpha_dummy_093 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_093, fv_syn_c0] using (nb057_compact_fv_empty_0087 f)

theorem nb057_wpp_notmem_0270 : (nb057_alpha_dummy_046) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_046, fv_syn_c0] using (nb057_compact_fv_empty_0088)

theorem nb057_wpp_notmem_0271 (f : Var) : (nb057_alpha_dummy_049 f) ∉ ((syn_c0)).fv := by
  simpa only [nb057_alpha_dummy_049, fv_syn_c0] using (nb057_compact_fv_empty_0089 f)

theorem nb057_compact_envfresh_0015 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_104) (nb057_alpha_dummy_107 f) (nb057_wpp_notmem_0250) (nb057_wpp_notmem_0251 f) (TEnvFresh.consFresh (nb057_alpha_dummy_103) (nb057_alpha_dummy_106 f) (nb057_wpp_notmem_0252) (nb057_wpp_notmem_0253 f) (TEnvFresh.consFresh (nb057_alpha_dummy_102) (nb057_alpha_dummy_105 f) (nb057_wpp_notmem_0254) (nb057_wpp_notmem_0255 f) (TEnvFresh.consFresh (nb057_alpha_dummy_100) (nb057_alpha_dummy_101 f) (nb057_wpp_notmem_0256) (nb057_wpp_notmem_0257 f) (TEnvFresh.consFresh (nb057_alpha_dummy_096) (nb057_alpha_dummy_098 f) (nb057_wpp_notmem_0258) (nb057_wpp_notmem_0259 f) (TEnvFresh.consFresh (nb057_alpha_dummy_097) (nb057_alpha_dummy_099 f) (nb057_wpp_notmem_0260) (nb057_wpp_notmem_0261 f) (TEnvFresh.consFresh (nb057_alpha_dummy_089) (nb057_alpha_dummy_091 f) (nb057_wpp_notmem_0262) (nb057_wpp_notmem_0263 f) (TEnvFresh.consFresh (nb057_alpha_dummy_088) (nb057_alpha_dummy_090 f) (nb057_wpp_notmem_0264) (nb057_wpp_notmem_0265 f) (TEnvFresh.consFresh (nb057_alpha_dummy_094) (nb057_alpha_dummy_095 f) (nb057_wpp_notmem_0266) (nb057_wpp_notmem_0267 f) (TEnvFresh.consFresh (nb057_alpha_dummy_092) (nb057_alpha_dummy_093 f) (nb057_wpp_notmem_0268) (nb057_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0270) (nb057_wpp_notmem_0271 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0156) (nb057_wpp_notmem_0157 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0158) (nb057_wpp_notmem_0159 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0160) (nb057_wpp_notmem_0161 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0162) (nb057_wpp_notmem_0163 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0164) (nb057_wpp_notmem_0165 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0046) (nb057_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0048) (nb057_wpp_notmem_0049 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0050) (nb057_wpp_notmem_0051 f a) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb057_wpp_refl_0015 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0015 f a)

noncomputable def nb057_split_alpha_0010 (f : Var) (a : Var) : TAlphaWff [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_102)) (syn_cun (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_105 f)) (syn_cun (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0099 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0097 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0099 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0097 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)), ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)), ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)), ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] (syn_c0) (nb057_wpp_refl_0015 f a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0111 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0109 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0110) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0111 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0109 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb057_wpp_notmem_0272 : (nb057_alpha_dummy_100) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_100, fv_syn_cnnc] using (nb057_compact_fv_empty_0074)

theorem nb057_wpp_notmem_0273 (f : Var) : (nb057_alpha_dummy_101 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_101, fv_syn_cnnc] using (nb057_compact_fv_empty_0075 f)

theorem nb057_wpp_notmem_0274 : (nb057_alpha_dummy_096) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_096, fv_syn_cnnc] using (nb057_compact_fv_empty_0076)

theorem nb057_wpp_notmem_0275 (f : Var) : (nb057_alpha_dummy_098 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_098, fv_syn_cnnc] using (nb057_compact_fv_empty_0077 f)

theorem nb057_wpp_notmem_0276 : (nb057_alpha_dummy_097) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_097, fv_syn_cnnc] using (nb057_compact_fv_empty_0078)

theorem nb057_wpp_notmem_0277 (f : Var) : (nb057_alpha_dummy_099 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_099, fv_syn_cnnc] using (nb057_compact_fv_empty_0079 f)

theorem nb057_wpp_notmem_0278 : (nb057_alpha_dummy_089) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_089, fv_syn_cnnc] using (nb057_compact_fv_empty_0080)

theorem nb057_wpp_notmem_0279 (f : Var) : (nb057_alpha_dummy_091 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_091, fv_syn_cnnc] using (nb057_compact_fv_empty_0081 f)

theorem nb057_wpp_notmem_0280 : (nb057_alpha_dummy_088) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_088, fv_syn_cnnc] using (nb057_compact_fv_empty_0082)

theorem nb057_wpp_notmem_0281 (f : Var) : (nb057_alpha_dummy_090 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_090, fv_syn_cnnc] using (nb057_compact_fv_empty_0083 f)

theorem nb057_wpp_notmem_0282 : (nb057_alpha_dummy_094) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_094, fv_syn_cnnc] using (nb057_compact_fv_empty_0084)

theorem nb057_wpp_notmem_0283 (f : Var) : (nb057_alpha_dummy_095 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_095, fv_syn_cnnc] using (nb057_compact_fv_empty_0085 f)

theorem nb057_wpp_notmem_0284 : (nb057_alpha_dummy_092) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_092, fv_syn_cnnc] using (nb057_compact_fv_empty_0086)

theorem nb057_wpp_notmem_0285 (f : Var) : (nb057_alpha_dummy_093 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_093, fv_syn_cnnc] using (nb057_compact_fv_empty_0087 f)

theorem nb057_wpp_notmem_0286 : (nb057_alpha_dummy_046) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_046, fv_syn_cnnc] using (nb057_compact_fv_empty_0088)

theorem nb057_wpp_notmem_0287 (f : Var) : (nb057_alpha_dummy_049 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb057_alpha_dummy_049, fv_syn_cnnc] using (nb057_compact_fv_empty_0089 f)

theorem nb057_compact_envfresh_0016 (f : Var) (a : Var) : TEnvFresh [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb057_alpha_dummy_100) (nb057_alpha_dummy_101 f) (nb057_wpp_notmem_0272) (nb057_wpp_notmem_0273 f) (TEnvFresh.consFresh (nb057_alpha_dummy_096) (nb057_alpha_dummy_098 f) (nb057_wpp_notmem_0274) (nb057_wpp_notmem_0275 f) (TEnvFresh.consFresh (nb057_alpha_dummy_097) (nb057_alpha_dummy_099 f) (nb057_wpp_notmem_0276) (nb057_wpp_notmem_0277 f) (TEnvFresh.consFresh (nb057_alpha_dummy_089) (nb057_alpha_dummy_091 f) (nb057_wpp_notmem_0278) (nb057_wpp_notmem_0279 f) (TEnvFresh.consFresh (nb057_alpha_dummy_088) (nb057_alpha_dummy_090 f) (nb057_wpp_notmem_0280) (nb057_wpp_notmem_0281 f) (TEnvFresh.consFresh (nb057_alpha_dummy_094) (nb057_alpha_dummy_095 f) (nb057_wpp_notmem_0282) (nb057_wpp_notmem_0283 f) (TEnvFresh.consFresh (nb057_alpha_dummy_092) (nb057_alpha_dummy_093 f) (nb057_wpp_notmem_0284) (nb057_wpp_notmem_0285 f) (TEnvFresh.consFresh (nb057_alpha_dummy_046) (nb057_alpha_dummy_049 f) (nb057_wpp_notmem_0286) (nb057_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb057_alpha_dummy_045) (nb057_alpha_dummy_048 f) (nb057_wpp_notmem_0180) (nb057_wpp_notmem_0181 f) (TEnvFresh.consFresh (nb057_alpha_dummy_044) (nb057_alpha_dummy_047 f) (nb057_wpp_notmem_0182) (nb057_wpp_notmem_0183 f) (TEnvFresh.consFresh (nb057_alpha_dummy_050) (nb057_alpha_dummy_051 f) (nb057_wpp_notmem_0184) (nb057_wpp_notmem_0185 f) (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f) (nb057_wpp_notmem_0186) (nb057_wpp_notmem_0187 f) (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f) (nb057_wpp_notmem_0188) (nb057_wpp_notmem_0189 f) (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0066) (nb057_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0068) (nb057_wpp_notmem_0069 f) (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a) (nb057_wpp_notmem_0070) (nb057_wpp_notmem_0071 f a) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb057_wpp_refl_0016 (f : Var) (a : Var) : TReflOn [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)), ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)), ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)), ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)), ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)), ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)), ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)), ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)), ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)), ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)), ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)), ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)), ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0016 f a)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
