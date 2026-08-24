import NAR4C071C001Part004

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

theorem nb071_compact_envfresh_0009 (x : Var) : TEnvFresh [((nb071_alpha_dummy_063), (nb071_alpha_dummy_064 x)), ((nb071_alpha_dummy_061), (nb071_alpha_dummy_062 x)), ((nb071_alpha_dummy_059), (nb071_alpha_dummy_060 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_063) (nb071_alpha_dummy_064 x) (nb071_wpp_notmem_0120) (nb071_wpp_notmem_0121 x) (TEnvFresh.consFresh (nb071_alpha_dummy_061) (nb071_alpha_dummy_062 x) (nb071_wpp_notmem_0122) (nb071_wpp_notmem_0123 x) (TEnvFresh.consFresh (nb071_alpha_dummy_059) (nb071_alpha_dummy_060 x) (nb071_wpp_notmem_0124) (nb071_wpp_notmem_0125 x) (TEnvFresh.consFresh (nb071_alpha_dummy_056) (nb071_alpha_dummy_058 x) (nb071_wpp_notmem_0126) (nb071_wpp_notmem_0127 x) (TEnvFresh.consFresh (nb071_alpha_dummy_055) (nb071_alpha_dummy_057 x) (nb071_wpp_notmem_0128) (nb071_wpp_notmem_0129 x) (TEnvFresh.consFresh (nb071_alpha_dummy_042) (nb071_alpha_dummy_044 x) (nb071_wpp_notmem_0130) (nb071_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb071_alpha_dummy_041) (nb071_alpha_dummy_043 x) (nb071_wpp_notmem_0132) (nb071_wpp_notmem_0133 x) (TEnvFresh.consFresh (nb071_alpha_dummy_045) (nb071_alpha_dummy_046 x) (nb071_wpp_notmem_0134) (nb071_wpp_notmem_0135 x) (TEnvFresh.consFresh (nb071_alpha_dummy_048) (nb071_alpha_dummy_050 x) (nb071_wpp_notmem_0136) (nb071_wpp_notmem_0137 x) (TEnvFresh.consFresh (nb071_alpha_dummy_047) (nb071_alpha_dummy_049 x) (nb071_wpp_notmem_0138) (nb071_wpp_notmem_0139 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0020) (nb071_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0022) (nb071_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0024) (nb071_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))

noncomputable def nb071_wpp_refl_0009 (x : Var) : TReflOn [((nb071_alpha_dummy_063), (nb071_alpha_dummy_064 x)), ((nb071_alpha_dummy_061), (nb071_alpha_dummy_062 x)), ((nb071_alpha_dummy_059), (nb071_alpha_dummy_060 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0009 x)

noncomputable def nb071_split_alpha_0005 (x : Var) : TAlphaWff [((nb071_alpha_dummy_061), (nb071_alpha_dummy_062 x)), ((nb071_alpha_dummy_059), (nb071_alpha_dummy_060 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_061)) (syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))) (Wff.neg (Wff.classMem (Class.cv (nb071_alpha_dummy_061)) (syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))))) (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_062 x)) (syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))) (Wff.neg (Wff.classMem (Class.cv (nb071_alpha_dummy_062 x)) (syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0055 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0053 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0069 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0067 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0065 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0063 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0061 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0059 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0056) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0057 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0057 x) 0)) (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0055 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0053 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0069 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0067 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0065 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0063 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0061 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0059 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0056) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0057 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0057 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaClass.cv (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_063), (nb071_alpha_dummy_064 x)), ((nb071_alpha_dummy_061), (nb071_alpha_dummy_062 x)), ((nb071_alpha_dummy_059), (nb071_alpha_dummy_060 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_c1c) (nb071_wpp_refl_0009 x))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0055 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0053 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0069 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0067 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0065 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0063 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0061 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0059 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0056) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0057 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0057 x) 0)) (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0055 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0053 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0069 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0067 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0065 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0063 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0061 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0059 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0056) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0057 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0057 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaClass.cv (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_063), (nb071_alpha_dummy_064 x)), ((nb071_alpha_dummy_061), (nb071_alpha_dummy_062 x)), ((nb071_alpha_dummy_059), (nb071_alpha_dummy_060 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_c1c) (nb071_wpp_refl_0009 x)))))))))))

theorem nb071_compact_fv_empty_0052 : (nb071_alpha_dummy_087) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0140 : (nb071_alpha_dummy_087) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_087, fv_syn_c1c] using (nb071_compact_fv_empty_0052)

theorem nb071_compact_fv_empty_0053 (x : Var) : (nb071_alpha_dummy_090 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0141 (x : Var) : (nb071_alpha_dummy_090 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_090, fv_syn_c1c] using (nb071_compact_fv_empty_0053 x)

theorem nb071_compact_fv_empty_0054 : (nb071_alpha_dummy_086) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0142 : (nb071_alpha_dummy_086) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_086, fv_syn_c1c] using (nb071_compact_fv_empty_0054)

theorem nb071_compact_fv_empty_0055 (x : Var) : (nb071_alpha_dummy_089 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0143 (x : Var) : (nb071_alpha_dummy_089 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_089, fv_syn_c1c] using (nb071_compact_fv_empty_0055 x)

theorem nb071_compact_fv_empty_0056 : (nb071_alpha_dummy_085) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0144 : (nb071_alpha_dummy_085) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_085, fv_syn_c1c] using (nb071_compact_fv_empty_0056)

theorem nb071_compact_fv_empty_0057 (x : Var) : (nb071_alpha_dummy_088 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0145 (x : Var) : (nb071_alpha_dummy_088 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_088, fv_syn_c1c] using (nb071_compact_fv_empty_0057 x)

theorem nb071_compact_fv_empty_0058 : (nb071_alpha_dummy_083) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0146 : (nb071_alpha_dummy_083) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_083, fv_syn_c1c] using (nb071_compact_fv_empty_0058)

theorem nb071_compact_fv_empty_0059 (x : Var) : (nb071_alpha_dummy_084 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0147 (x : Var) : (nb071_alpha_dummy_084 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_084, fv_syn_c1c] using (nb071_compact_fv_empty_0059 x)

theorem nb071_compact_fv_empty_0060 : (nb071_alpha_dummy_079) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0148 : (nb071_alpha_dummy_079) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_079, fv_syn_c1c] using (nb071_compact_fv_empty_0060)

theorem nb071_compact_fv_empty_0061 (x : Var) : (nb071_alpha_dummy_081 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0149 (x : Var) : (nb071_alpha_dummy_081 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_081, fv_syn_c1c] using (nb071_compact_fv_empty_0061 x)

theorem nb071_compact_fv_empty_0062 : (nb071_alpha_dummy_080) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0150 : (nb071_alpha_dummy_080) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_080, fv_syn_c1c] using (nb071_compact_fv_empty_0062)

theorem nb071_compact_fv_empty_0063 (x : Var) : (nb071_alpha_dummy_082 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0151 (x : Var) : (nb071_alpha_dummy_082 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_082, fv_syn_c1c] using (nb071_compact_fv_empty_0063 x)

theorem nb071_compact_fv_empty_0064 : (nb071_alpha_dummy_072) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0152 : (nb071_alpha_dummy_072) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_072, fv_syn_c1c] using (nb071_compact_fv_empty_0064)

theorem nb071_compact_fv_empty_0065 (x : Var) : (nb071_alpha_dummy_074 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0153 (x : Var) : (nb071_alpha_dummy_074 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_074, fv_syn_c1c] using (nb071_compact_fv_empty_0065 x)

theorem nb071_compact_fv_empty_0066 : (nb071_alpha_dummy_071) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0154 : (nb071_alpha_dummy_071) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_071, fv_syn_c1c] using (nb071_compact_fv_empty_0066)

theorem nb071_compact_fv_empty_0067 (x : Var) : (nb071_alpha_dummy_073 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0155 (x : Var) : (nb071_alpha_dummy_073 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_073, fv_syn_c1c] using (nb071_compact_fv_empty_0067 x)

theorem nb071_compact_fv_empty_0068 : (nb071_alpha_dummy_077) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0156 : (nb071_alpha_dummy_077) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_077, fv_syn_c1c] using (nb071_compact_fv_empty_0068)

theorem nb071_compact_fv_empty_0069 (x : Var) : (nb071_alpha_dummy_078 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0157 (x : Var) : (nb071_alpha_dummy_078 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_078, fv_syn_c1c] using (nb071_compact_fv_empty_0069 x)

theorem nb071_compact_fv_empty_0070 : (nb071_alpha_dummy_075) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0158 : (nb071_alpha_dummy_075) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_075, fv_syn_c1c] using (nb071_compact_fv_empty_0070)

theorem nb071_compact_fv_empty_0071 (x : Var) : (nb071_alpha_dummy_076 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0159 (x : Var) : (nb071_alpha_dummy_076 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_076, fv_syn_c1c] using (nb071_compact_fv_empty_0071 x)

theorem nb071_compact_envfresh_0010 (x : Var) : TEnvFresh [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)), ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)), ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)), ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_087) (nb071_alpha_dummy_090 x) (nb071_wpp_notmem_0140) (nb071_wpp_notmem_0141 x) (TEnvFresh.consFresh (nb071_alpha_dummy_086) (nb071_alpha_dummy_089 x) (nb071_wpp_notmem_0142) (nb071_wpp_notmem_0143 x) (TEnvFresh.consFresh (nb071_alpha_dummy_085) (nb071_alpha_dummy_088 x) (nb071_wpp_notmem_0144) (nb071_wpp_notmem_0145 x) (TEnvFresh.consFresh (nb071_alpha_dummy_083) (nb071_alpha_dummy_084 x) (nb071_wpp_notmem_0146) (nb071_wpp_notmem_0147 x) (TEnvFresh.consFresh (nb071_alpha_dummy_079) (nb071_alpha_dummy_081 x) (nb071_wpp_notmem_0148) (nb071_wpp_notmem_0149 x) (TEnvFresh.consFresh (nb071_alpha_dummy_080) (nb071_alpha_dummy_082 x) (nb071_wpp_notmem_0150) (nb071_wpp_notmem_0151 x) (TEnvFresh.consFresh (nb071_alpha_dummy_072) (nb071_alpha_dummy_074 x) (nb071_wpp_notmem_0152) (nb071_wpp_notmem_0153 x) (TEnvFresh.consFresh (nb071_alpha_dummy_071) (nb071_alpha_dummy_073 x) (nb071_wpp_notmem_0154) (nb071_wpp_notmem_0155 x) (TEnvFresh.consFresh (nb071_alpha_dummy_077) (nb071_alpha_dummy_078 x) (nb071_wpp_notmem_0156) (nb071_wpp_notmem_0157 x) (TEnvFresh.consFresh (nb071_alpha_dummy_075) (nb071_alpha_dummy_076 x) (nb071_wpp_notmem_0158) (nb071_wpp_notmem_0159 x) (TEnvFresh.consFresh (nb071_alpha_dummy_056) (nb071_alpha_dummy_058 x) (nb071_wpp_notmem_0126) (nb071_wpp_notmem_0127 x) (TEnvFresh.consFresh (nb071_alpha_dummy_055) (nb071_alpha_dummy_057 x) (nb071_wpp_notmem_0128) (nb071_wpp_notmem_0129 x) (TEnvFresh.consFresh (nb071_alpha_dummy_042) (nb071_alpha_dummy_044 x) (nb071_wpp_notmem_0130) (nb071_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb071_alpha_dummy_041) (nb071_alpha_dummy_043 x) (nb071_wpp_notmem_0132) (nb071_wpp_notmem_0133 x) (TEnvFresh.consFresh (nb071_alpha_dummy_045) (nb071_alpha_dummy_046 x) (nb071_wpp_notmem_0134) (nb071_wpp_notmem_0135 x) (TEnvFresh.consFresh (nb071_alpha_dummy_048) (nb071_alpha_dummy_050 x) (nb071_wpp_notmem_0136) (nb071_wpp_notmem_0137 x) (TEnvFresh.consFresh (nb071_alpha_dummy_047) (nb071_alpha_dummy_049 x) (nb071_wpp_notmem_0138) (nb071_wpp_notmem_0139 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0020) (nb071_wpp_notmem_0021 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0022) (nb071_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0024) (nb071_wpp_notmem_0025 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb071_wpp_refl_0010 (x : Var) : TReflOn [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)), ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)), ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)), ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0010 x)

theorem nb071_wpp_notmem_0160 : (nb071_alpha_dummy_087) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_087, fv_syn_c0] using (nb071_compact_fv_empty_0052)

theorem nb071_wpp_notmem_0161 (x : Var) : (nb071_alpha_dummy_090 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_090, fv_syn_c0] using (nb071_compact_fv_empty_0053 x)

theorem nb071_wpp_notmem_0162 : (nb071_alpha_dummy_086) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_086, fv_syn_c0] using (nb071_compact_fv_empty_0054)

theorem nb071_wpp_notmem_0163 (x : Var) : (nb071_alpha_dummy_089 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_089, fv_syn_c0] using (nb071_compact_fv_empty_0055 x)

theorem nb071_wpp_notmem_0164 : (nb071_alpha_dummy_085) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_085, fv_syn_c0] using (nb071_compact_fv_empty_0056)

theorem nb071_wpp_notmem_0165 (x : Var) : (nb071_alpha_dummy_088 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_088, fv_syn_c0] using (nb071_compact_fv_empty_0057 x)

theorem nb071_wpp_notmem_0166 : (nb071_alpha_dummy_083) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_083, fv_syn_c0] using (nb071_compact_fv_empty_0058)

theorem nb071_wpp_notmem_0167 (x : Var) : (nb071_alpha_dummy_084 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_084, fv_syn_c0] using (nb071_compact_fv_empty_0059 x)

theorem nb071_wpp_notmem_0168 : (nb071_alpha_dummy_079) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_079, fv_syn_c0] using (nb071_compact_fv_empty_0060)

theorem nb071_wpp_notmem_0169 (x : Var) : (nb071_alpha_dummy_081 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_081, fv_syn_c0] using (nb071_compact_fv_empty_0061 x)

theorem nb071_wpp_notmem_0170 : (nb071_alpha_dummy_080) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_080, fv_syn_c0] using (nb071_compact_fv_empty_0062)

theorem nb071_wpp_notmem_0171 (x : Var) : (nb071_alpha_dummy_082 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_082, fv_syn_c0] using (nb071_compact_fv_empty_0063 x)

theorem nb071_wpp_notmem_0172 : (nb071_alpha_dummy_072) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_072, fv_syn_c0] using (nb071_compact_fv_empty_0064)

theorem nb071_wpp_notmem_0173 (x : Var) : (nb071_alpha_dummy_074 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_074, fv_syn_c0] using (nb071_compact_fv_empty_0065 x)

theorem nb071_wpp_notmem_0174 : (nb071_alpha_dummy_071) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_071, fv_syn_c0] using (nb071_compact_fv_empty_0066)

theorem nb071_wpp_notmem_0175 (x : Var) : (nb071_alpha_dummy_073 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_073, fv_syn_c0] using (nb071_compact_fv_empty_0067 x)

theorem nb071_wpp_notmem_0176 : (nb071_alpha_dummy_077) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_077, fv_syn_c0] using (nb071_compact_fv_empty_0068)

theorem nb071_wpp_notmem_0177 (x : Var) : (nb071_alpha_dummy_078 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_078, fv_syn_c0] using (nb071_compact_fv_empty_0069 x)

theorem nb071_wpp_notmem_0178 : (nb071_alpha_dummy_075) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_075, fv_syn_c0] using (nb071_compact_fv_empty_0070)

theorem nb071_wpp_notmem_0179 (x : Var) : (nb071_alpha_dummy_076 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_076, fv_syn_c0] using (nb071_compact_fv_empty_0071 x)

theorem nb071_wpp_notmem_0180 : (nb071_alpha_dummy_056) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_056, fv_syn_c0] using (nb071_compact_fv_empty_0046)

theorem nb071_wpp_notmem_0181 (x : Var) : (nb071_alpha_dummy_058 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_058, fv_syn_c0] using (nb071_compact_fv_empty_0047 x)

theorem nb071_wpp_notmem_0182 : (nb071_alpha_dummy_055) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_055, fv_syn_c0] using (nb071_compact_fv_empty_0048)

theorem nb071_wpp_notmem_0183 (x : Var) : (nb071_alpha_dummy_057 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_057, fv_syn_c0] using (nb071_compact_fv_empty_0049 x)

theorem nb071_wpp_notmem_0184 : (nb071_alpha_dummy_042) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_042, fv_syn_c0] using (nb071_compact_fv_empty_0050)

theorem nb071_wpp_notmem_0185 (x : Var) : (nb071_alpha_dummy_044 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_044, fv_syn_c0] using (nb071_compact_fv_empty_0051 x)

theorem nb071_wpp_notmem_0186 : (nb071_alpha_dummy_041) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_041, fv_syn_c0] using (nb071_compact_fv_empty_0032)

theorem nb071_wpp_notmem_0187 (x : Var) : (nb071_alpha_dummy_043 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_043, fv_syn_c0] using (nb071_compact_fv_empty_0033 x)

theorem nb071_wpp_notmem_0188 : (nb071_alpha_dummy_045) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_045, fv_syn_c0] using (nb071_compact_fv_empty_0034)

theorem nb071_wpp_notmem_0189 (x : Var) : (nb071_alpha_dummy_046 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_046, fv_syn_c0] using (nb071_compact_fv_empty_0035 x)

theorem nb071_wpp_notmem_0190 : (nb071_alpha_dummy_048) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_048, fv_syn_c0] using (nb071_compact_fv_empty_0036)

theorem nb071_wpp_notmem_0191 (x : Var) : (nb071_alpha_dummy_050 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_050, fv_syn_c0] using (nb071_compact_fv_empty_0037 x)

theorem nb071_wpp_notmem_0192 : (nb071_alpha_dummy_047) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_047, fv_syn_c0] using (nb071_compact_fv_empty_0038)

theorem nb071_wpp_notmem_0193 (x : Var) : (nb071_alpha_dummy_049 x) ∉ ((syn_c0)).fv := by
  simpa only [nb071_alpha_dummy_049, fv_syn_c0] using (nb071_compact_fv_empty_0039 x)

theorem nb071_compact_envfresh_0011 (x : Var) : TEnvFresh [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)), ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)), ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)), ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_087) (nb071_alpha_dummy_090 x) (nb071_wpp_notmem_0160) (nb071_wpp_notmem_0161 x) (TEnvFresh.consFresh (nb071_alpha_dummy_086) (nb071_alpha_dummy_089 x) (nb071_wpp_notmem_0162) (nb071_wpp_notmem_0163 x) (TEnvFresh.consFresh (nb071_alpha_dummy_085) (nb071_alpha_dummy_088 x) (nb071_wpp_notmem_0164) (nb071_wpp_notmem_0165 x) (TEnvFresh.consFresh (nb071_alpha_dummy_083) (nb071_alpha_dummy_084 x) (nb071_wpp_notmem_0166) (nb071_wpp_notmem_0167 x) (TEnvFresh.consFresh (nb071_alpha_dummy_079) (nb071_alpha_dummy_081 x) (nb071_wpp_notmem_0168) (nb071_wpp_notmem_0169 x) (TEnvFresh.consFresh (nb071_alpha_dummy_080) (nb071_alpha_dummy_082 x) (nb071_wpp_notmem_0170) (nb071_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb071_alpha_dummy_072) (nb071_alpha_dummy_074 x) (nb071_wpp_notmem_0172) (nb071_wpp_notmem_0173 x) (TEnvFresh.consFresh (nb071_alpha_dummy_071) (nb071_alpha_dummy_073 x) (nb071_wpp_notmem_0174) (nb071_wpp_notmem_0175 x) (TEnvFresh.consFresh (nb071_alpha_dummy_077) (nb071_alpha_dummy_078 x) (nb071_wpp_notmem_0176) (nb071_wpp_notmem_0177 x) (TEnvFresh.consFresh (nb071_alpha_dummy_075) (nb071_alpha_dummy_076 x) (nb071_wpp_notmem_0178) (nb071_wpp_notmem_0179 x) (TEnvFresh.consFresh (nb071_alpha_dummy_056) (nb071_alpha_dummy_058 x) (nb071_wpp_notmem_0180) (nb071_wpp_notmem_0181 x) (TEnvFresh.consFresh (nb071_alpha_dummy_055) (nb071_alpha_dummy_057 x) (nb071_wpp_notmem_0182) (nb071_wpp_notmem_0183 x) (TEnvFresh.consFresh (nb071_alpha_dummy_042) (nb071_alpha_dummy_044 x) (nb071_wpp_notmem_0184) (nb071_wpp_notmem_0185 x) (TEnvFresh.consFresh (nb071_alpha_dummy_041) (nb071_alpha_dummy_043 x) (nb071_wpp_notmem_0186) (nb071_wpp_notmem_0187 x) (TEnvFresh.consFresh (nb071_alpha_dummy_045) (nb071_alpha_dummy_046 x) (nb071_wpp_notmem_0188) (nb071_wpp_notmem_0189 x) (TEnvFresh.consFresh (nb071_alpha_dummy_048) (nb071_alpha_dummy_050 x) (nb071_wpp_notmem_0190) (nb071_wpp_notmem_0191 x) (TEnvFresh.consFresh (nb071_alpha_dummy_047) (nb071_alpha_dummy_049 x) (nb071_wpp_notmem_0192) (nb071_wpp_notmem_0193 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0046) (nb071_wpp_notmem_0047 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0048) (nb071_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0050) (nb071_wpp_notmem_0051 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb071_wpp_refl_0011 (x : Var) : TReflOn [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)), ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)), ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)), ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0011 x)

noncomputable def nb071_split_alpha_0006 (x : Var) : TAlphaWff [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)), ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)), ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)), ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_085)) (syn_cun (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb071_alpha_dummy_089 x)) (Class.cv (nb071_alpha_dummy_090 x))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_088 x)) (syn_cun (Class.cv (nb071_alpha_dummy_089 x)) (Class.cv (nb071_alpha_dummy_090 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0084) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0085 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0083 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0089 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0087 x) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0084) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0085 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0082) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0083 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0089 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0087 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)), ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)), ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)), ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_c0) (nb071_wpp_refl_0011 x))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0093 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0091 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0093 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0091 x) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0097 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0097 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0095 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb071_wpp_notmem_0194 : (nb071_alpha_dummy_083) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_083, fv_syn_cnnc] using (nb071_compact_fv_empty_0058)

theorem nb071_wpp_notmem_0195 (x : Var) : (nb071_alpha_dummy_084 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_084, fv_syn_cnnc] using (nb071_compact_fv_empty_0059 x)

theorem nb071_wpp_notmem_0196 : (nb071_alpha_dummy_079) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_079, fv_syn_cnnc] using (nb071_compact_fv_empty_0060)

theorem nb071_wpp_notmem_0197 (x : Var) : (nb071_alpha_dummy_081 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_081, fv_syn_cnnc] using (nb071_compact_fv_empty_0061 x)

theorem nb071_wpp_notmem_0198 : (nb071_alpha_dummy_080) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_080, fv_syn_cnnc] using (nb071_compact_fv_empty_0062)

theorem nb071_wpp_notmem_0199 (x : Var) : (nb071_alpha_dummy_082 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_082, fv_syn_cnnc] using (nb071_compact_fv_empty_0063 x)

theorem nb071_wpp_notmem_0200 : (nb071_alpha_dummy_072) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_072, fv_syn_cnnc] using (nb071_compact_fv_empty_0064)

theorem nb071_wpp_notmem_0201 (x : Var) : (nb071_alpha_dummy_074 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_074, fv_syn_cnnc] using (nb071_compact_fv_empty_0065 x)

theorem nb071_wpp_notmem_0202 : (nb071_alpha_dummy_071) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_071, fv_syn_cnnc] using (nb071_compact_fv_empty_0066)

theorem nb071_wpp_notmem_0203 (x : Var) : (nb071_alpha_dummy_073 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_073, fv_syn_cnnc] using (nb071_compact_fv_empty_0067 x)

theorem nb071_wpp_notmem_0204 : (nb071_alpha_dummy_077) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_077, fv_syn_cnnc] using (nb071_compact_fv_empty_0068)

theorem nb071_wpp_notmem_0205 (x : Var) : (nb071_alpha_dummy_078 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_078, fv_syn_cnnc] using (nb071_compact_fv_empty_0069 x)

theorem nb071_wpp_notmem_0206 : (nb071_alpha_dummy_075) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_075, fv_syn_cnnc] using (nb071_compact_fv_empty_0070)

theorem nb071_wpp_notmem_0207 (x : Var) : (nb071_alpha_dummy_076 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_076, fv_syn_cnnc] using (nb071_compact_fv_empty_0071 x)

theorem nb071_wpp_notmem_0208 : (nb071_alpha_dummy_056) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_056, fv_syn_cnnc] using (nb071_compact_fv_empty_0046)

theorem nb071_wpp_notmem_0209 (x : Var) : (nb071_alpha_dummy_058 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_058, fv_syn_cnnc] using (nb071_compact_fv_empty_0047 x)

theorem nb071_wpp_notmem_0210 : (nb071_alpha_dummy_055) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_055, fv_syn_cnnc] using (nb071_compact_fv_empty_0048)

theorem nb071_wpp_notmem_0211 (x : Var) : (nb071_alpha_dummy_057 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_057, fv_syn_cnnc] using (nb071_compact_fv_empty_0049 x)

theorem nb071_wpp_notmem_0212 : (nb071_alpha_dummy_042) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_042, fv_syn_cnnc] using (nb071_compact_fv_empty_0050)

theorem nb071_wpp_notmem_0213 (x : Var) : (nb071_alpha_dummy_044 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_044, fv_syn_cnnc] using (nb071_compact_fv_empty_0051 x)

theorem nb071_wpp_notmem_0214 : (nb071_alpha_dummy_041) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_041, fv_syn_cnnc] using (nb071_compact_fv_empty_0032)

theorem nb071_wpp_notmem_0215 (x : Var) : (nb071_alpha_dummy_043 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_043, fv_syn_cnnc] using (nb071_compact_fv_empty_0033 x)

theorem nb071_wpp_notmem_0216 : (nb071_alpha_dummy_045) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_045, fv_syn_cnnc] using (nb071_compact_fv_empty_0034)

theorem nb071_wpp_notmem_0217 (x : Var) : (nb071_alpha_dummy_046 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_046, fv_syn_cnnc] using (nb071_compact_fv_empty_0035 x)

theorem nb071_wpp_notmem_0218 : (nb071_alpha_dummy_048) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_048, fv_syn_cnnc] using (nb071_compact_fv_empty_0036)

theorem nb071_wpp_notmem_0219 (x : Var) : (nb071_alpha_dummy_050 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_050, fv_syn_cnnc] using (nb071_compact_fv_empty_0037 x)

theorem nb071_wpp_notmem_0220 : (nb071_alpha_dummy_047) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_047, fv_syn_cnnc] using (nb071_compact_fv_empty_0038)

theorem nb071_wpp_notmem_0221 (x : Var) : (nb071_alpha_dummy_049 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb071_alpha_dummy_049, fv_syn_cnnc] using (nb071_compact_fv_empty_0039 x)

theorem nb071_compact_envfresh_0012 (x : Var) : TEnvFresh [((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb071_alpha_dummy_083) (nb071_alpha_dummy_084 x) (nb071_wpp_notmem_0194) (nb071_wpp_notmem_0195 x) (TEnvFresh.consFresh (nb071_alpha_dummy_079) (nb071_alpha_dummy_081 x) (nb071_wpp_notmem_0196) (nb071_wpp_notmem_0197 x) (TEnvFresh.consFresh (nb071_alpha_dummy_080) (nb071_alpha_dummy_082 x) (nb071_wpp_notmem_0198) (nb071_wpp_notmem_0199 x) (TEnvFresh.consFresh (nb071_alpha_dummy_072) (nb071_alpha_dummy_074 x) (nb071_wpp_notmem_0200) (nb071_wpp_notmem_0201 x) (TEnvFresh.consFresh (nb071_alpha_dummy_071) (nb071_alpha_dummy_073 x) (nb071_wpp_notmem_0202) (nb071_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb071_alpha_dummy_077) (nb071_alpha_dummy_078 x) (nb071_wpp_notmem_0204) (nb071_wpp_notmem_0205 x) (TEnvFresh.consFresh (nb071_alpha_dummy_075) (nb071_alpha_dummy_076 x) (nb071_wpp_notmem_0206) (nb071_wpp_notmem_0207 x) (TEnvFresh.consFresh (nb071_alpha_dummy_056) (nb071_alpha_dummy_058 x) (nb071_wpp_notmem_0208) (nb071_wpp_notmem_0209 x) (TEnvFresh.consFresh (nb071_alpha_dummy_055) (nb071_alpha_dummy_057 x) (nb071_wpp_notmem_0210) (nb071_wpp_notmem_0211 x) (TEnvFresh.consFresh (nb071_alpha_dummy_042) (nb071_alpha_dummy_044 x) (nb071_wpp_notmem_0212) (nb071_wpp_notmem_0213 x) (TEnvFresh.consFresh (nb071_alpha_dummy_041) (nb071_alpha_dummy_043 x) (nb071_wpp_notmem_0214) (nb071_wpp_notmem_0215 x) (TEnvFresh.consFresh (nb071_alpha_dummy_045) (nb071_alpha_dummy_046 x) (nb071_wpp_notmem_0216) (nb071_wpp_notmem_0217 x) (TEnvFresh.consFresh (nb071_alpha_dummy_048) (nb071_alpha_dummy_050 x) (nb071_wpp_notmem_0218) (nb071_wpp_notmem_0219 x) (TEnvFresh.consFresh (nb071_alpha_dummy_047) (nb071_alpha_dummy_049 x) (nb071_wpp_notmem_0220) (nb071_wpp_notmem_0221 x) (TEnvFresh.consFresh (nb071_alpha_dummy_001) (nb071_alpha_dummy_002 x) (nb071_wpp_notmem_0066) (nb071_wpp_notmem_0067 x) (TEnvFresh.consFresh (nb071_alpha_dummy_000) x (nb071_wpp_notmem_0068) (nb071_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb071_alpha_dummy_003) (nb071_alpha_dummy_004 x) (nb071_wpp_notmem_0070) (nb071_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb071_wpp_refl_0012 (x : Var) : TReflOn [((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb071_compact_envfresh_0012 x)

noncomputable def nb071_split_alpha_0007 (x : Var) : TAlphaWff [((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (Class.cv (nb071_alpha_dummy_072))) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_080)) (syn_cif (Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (syn_cnnc)) (syn_cplc (Class.cv (nb071_alpha_dummy_079)) (syn_c1c)) (Class.cv (nb071_alpha_dummy_079)))))) (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (Class.cv (nb071_alpha_dummy_074 x))) (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_082 x)) (syn_cif (Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (syn_cnnc)) (syn_cplc (Class.cv (nb071_alpha_dummy_081 x)) (syn_c1c)) (Class.cv (nb071_alpha_dummy_081 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0077 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0076) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0077 x) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_072))).fv) (by decide)) (freshVar_injective (((Class.cv (nb071_alpha_dummy_074 x))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0080) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0081 x) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0081 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_087), (nb071_alpha_dummy_090 x)), ((nb071_alpha_dummy_086), (nb071_alpha_dummy_089 x)), ((nb071_alpha_dummy_085), (nb071_alpha_dummy_088 x)), ((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_c1c) (nb071_wpp_refl_0010 x))) (TAlphaWff.neg (TAlphaWff.neg (nb071_split_alpha_0006 x)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_cnnc) (nb071_wpp_refl_0012 x))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0079 x) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_083), (nb071_alpha_dummy_084 x)), ((nb071_alpha_dummy_079), (nb071_alpha_dummy_081 x)), ((nb071_alpha_dummy_080), (nb071_alpha_dummy_082 x)), ((nb071_alpha_dummy_072), (nb071_alpha_dummy_074 x)), ((nb071_alpha_dummy_071), (nb071_alpha_dummy_073 x)), ((nb071_alpha_dummy_077), (nb071_alpha_dummy_078 x)), ((nb071_alpha_dummy_075), (nb071_alpha_dummy_076 x)), ((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)), ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)), ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)), ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)), ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)), ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)), ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)), ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))] (syn_cnnc) (nb071_wpp_refl_0012 x))))))))))))

theorem nb071_compact_fv_empty_0072 : (nb071_alpha_dummy_105) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0222 : (nb071_alpha_dummy_105) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_105, fv_syn_c1c] using (nb071_compact_fv_empty_0072)

theorem nb071_compact_fv_empty_0073 (x : Var) : (nb071_alpha_dummy_106 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0223 (x : Var) : (nb071_alpha_dummy_106 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_106, fv_syn_c1c] using (nb071_compact_fv_empty_0073 x)

theorem nb071_compact_fv_empty_0074 : (nb071_alpha_dummy_103) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0224 : (nb071_alpha_dummy_103) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_103, fv_syn_c1c] using (nb071_compact_fv_empty_0074)

theorem nb071_compact_fv_empty_0075 (x : Var) : (nb071_alpha_dummy_104 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb071_wpp_notmem_0225 (x : Var) : (nb071_alpha_dummy_104 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb071_alpha_dummy_104, fv_syn_c1c] using (nb071_compact_fv_empty_0075 x)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
