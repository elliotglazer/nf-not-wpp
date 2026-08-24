import NAR4C060C001Part005

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

theorem nb060_wpp_notmem_0105 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : (nb060_alpha_dummy_006 x y z r a) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_006, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0025 x y z r a)

theorem nb060_compact_envfresh_0006 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)), ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)), ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)), ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)), ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_039) (nb060_alpha_dummy_040 r a) (nb060_wpp_notmem_0090) (nb060_wpp_notmem_0091 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_008) (nb060_alpha_dummy_010 r a) (nb060_wpp_notmem_0092) (nb060_wpp_notmem_0093 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_007) (nb060_alpha_dummy_009 r a) (nb060_wpp_notmem_0094) (nb060_wpp_notmem_0095 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_037) (nb060_alpha_dummy_038 r a) (nb060_wpp_notmem_0096) (nb060_wpp_notmem_0097 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_011) (nb060_alpha_dummy_012 r a) (nb060_wpp_notmem_0098) (nb060_wpp_notmem_0099 r a) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0100) (nb060_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0102) (nb060_wpp_notmem_0103 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0104) (nb060_wpp_notmem_0105 x y z r a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb060_wpp_refl_0006 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)), ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)), ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)), ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)), ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0006 x y z r a)

noncomputable def nb060_split_alpha_0004 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r) : TAlphaWff [((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.classEq (Class.cv (nb060_alpha_dummy_005)) (syn_cop (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_000)))) (Wff.classEq (Class.cv (nb060_alpha_dummy_006 x y z r a)) (syn_cop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0002) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0003 x y z r a) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0000) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0001 x y z r a) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0001 x y z r a dv_a_r))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0001 x y z r a dv_a_r))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0037 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0035 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0003 x y z r a))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)), ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)), ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)), ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)), ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb060_wpp_refl_0006 x y z r a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0032) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0034 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0036) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0037 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0033) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0035 r a) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0003 x y z r a))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)), ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)), ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)), ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)), ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb060_wpp_refl_0006 x y z r a)))))))))))))))))))))))))))))

theorem nb060_compact_fv_empty_0032 : (nb060_alpha_dummy_059) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0106 : (nb060_alpha_dummy_059) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_059, fv_syn_c1c] using (nb060_compact_fv_empty_0032)

theorem nb060_compact_fv_empty_0033 (x : Var) (y : Var) : (nb060_alpha_dummy_062 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0107 (x : Var) (y : Var) : (nb060_alpha_dummy_062 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_062, fv_syn_c1c] using (nb060_compact_fv_empty_0033 x y)

theorem nb060_compact_fv_empty_0034 : (nb060_alpha_dummy_058) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0108 : (nb060_alpha_dummy_058) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_058, fv_syn_c1c] using (nb060_compact_fv_empty_0034)

theorem nb060_compact_fv_empty_0035 (x : Var) (y : Var) : (nb060_alpha_dummy_061 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0109 (x : Var) (y : Var) : (nb060_alpha_dummy_061 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_061, fv_syn_c1c] using (nb060_compact_fv_empty_0035 x y)

theorem nb060_compact_fv_empty_0036 : (nb060_alpha_dummy_057) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0110 : (nb060_alpha_dummy_057) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_057, fv_syn_c1c] using (nb060_compact_fv_empty_0036)

theorem nb060_compact_fv_empty_0037 (x : Var) (y : Var) : (nb060_alpha_dummy_060 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0111 (x : Var) (y : Var) : (nb060_alpha_dummy_060 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_060, fv_syn_c1c] using (nb060_compact_fv_empty_0037 x y)

theorem nb060_compact_fv_empty_0038 : (nb060_alpha_dummy_055) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0112 : (nb060_alpha_dummy_055) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_055, fv_syn_c1c] using (nb060_compact_fv_empty_0038)

theorem nb060_compact_fv_empty_0039 (x : Var) (y : Var) : (nb060_alpha_dummy_056 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0113 (x : Var) (y : Var) : (nb060_alpha_dummy_056 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_056, fv_syn_c1c] using (nb060_compact_fv_empty_0039 x y)

theorem nb060_compact_fv_empty_0040 : (nb060_alpha_dummy_051) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0114 : (nb060_alpha_dummy_051) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_051, fv_syn_c1c] using (nb060_compact_fv_empty_0040)

theorem nb060_compact_fv_empty_0041 (x : Var) (y : Var) : (nb060_alpha_dummy_053 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0115 (x : Var) (y : Var) : (nb060_alpha_dummy_053 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_053, fv_syn_c1c] using (nb060_compact_fv_empty_0041 x y)

theorem nb060_compact_fv_empty_0042 : (nb060_alpha_dummy_052) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0116 : (nb060_alpha_dummy_052) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_052, fv_syn_c1c] using (nb060_compact_fv_empty_0042)

theorem nb060_compact_fv_empty_0043 (x : Var) (y : Var) : (nb060_alpha_dummy_054 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0117 (x : Var) (y : Var) : (nb060_alpha_dummy_054 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_054, fv_syn_c1c] using (nb060_compact_fv_empty_0043 x y)

theorem nb060_compact_fv_empty_0044 : (nb060_alpha_dummy_044) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0118 : (nb060_alpha_dummy_044) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_044, fv_syn_c1c] using (nb060_compact_fv_empty_0044)

theorem nb060_compact_fv_empty_0045 (x : Var) (y : Var) : (nb060_alpha_dummy_046 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0119 (x : Var) (y : Var) : (nb060_alpha_dummy_046 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_046, fv_syn_c1c] using (nb060_compact_fv_empty_0045 x y)

theorem nb060_compact_fv_empty_0046 : (nb060_alpha_dummy_043) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0120 : (nb060_alpha_dummy_043) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_043, fv_syn_c1c] using (nb060_compact_fv_empty_0046)

theorem nb060_compact_fv_empty_0047 (x : Var) (y : Var) : (nb060_alpha_dummy_045 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0121 (x : Var) (y : Var) : (nb060_alpha_dummy_045 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_045, fv_syn_c1c] using (nb060_compact_fv_empty_0047 x y)

theorem nb060_compact_fv_empty_0048 : (nb060_alpha_dummy_049) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0122 : (nb060_alpha_dummy_049) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_049, fv_syn_c1c] using (nb060_compact_fv_empty_0048)

theorem nb060_compact_fv_empty_0049 (x : Var) (y : Var) : (nb060_alpha_dummy_050 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0123 (x : Var) (y : Var) : (nb060_alpha_dummy_050 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_050, fv_syn_c1c] using (nb060_compact_fv_empty_0049 x y)

theorem nb060_compact_fv_empty_0050 : (nb060_alpha_dummy_047) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0124 : (nb060_alpha_dummy_047) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_047, fv_syn_c1c] using (nb060_compact_fv_empty_0050)

theorem nb060_compact_fv_empty_0051 (x : Var) (y : Var) : (nb060_alpha_dummy_048 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0125 (x : Var) (y : Var) : (nb060_alpha_dummy_048 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_048, fv_syn_c1c] using (nb060_compact_fv_empty_0051 x y)

theorem nb060_compact_fv_empty_0052 : (nb060_alpha_dummy_004) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0126 : (nb060_alpha_dummy_004) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_004, fv_syn_c1c] using (nb060_compact_fv_empty_0052)

theorem nb060_compact_fv_empty_0053 (z : Var) : z ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0127 (z : Var) : z ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb060_compact_fv_empty_0053 z)

theorem nb060_compact_fv_empty_0054 : (nb060_alpha_dummy_003) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0128 : (nb060_alpha_dummy_003) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_003, fv_syn_c1c] using (nb060_compact_fv_empty_0054)

theorem nb060_compact_fv_empty_0055 (y : Var) : y ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0129 (y : Var) : y ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb060_compact_fv_empty_0055 y)

theorem nb060_compact_fv_empty_0056 : (nb060_alpha_dummy_002) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0130 : (nb060_alpha_dummy_002) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_002, fv_syn_c1c] using (nb060_compact_fv_empty_0056)

theorem nb060_compact_fv_empty_0057 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0131 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb060_compact_fv_empty_0057 x)

theorem nb060_compact_envfresh_0007 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_059) (nb060_alpha_dummy_062 x y) (nb060_wpp_notmem_0106) (nb060_wpp_notmem_0107 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_058) (nb060_alpha_dummy_061 x y) (nb060_wpp_notmem_0108) (nb060_wpp_notmem_0109 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_057) (nb060_alpha_dummy_060 x y) (nb060_wpp_notmem_0110) (nb060_wpp_notmem_0111 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_055) (nb060_alpha_dummy_056 x y) (nb060_wpp_notmem_0112) (nb060_wpp_notmem_0113 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_051) (nb060_alpha_dummy_053 x y) (nb060_wpp_notmem_0114) (nb060_wpp_notmem_0115 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_052) (nb060_alpha_dummy_054 x y) (nb060_wpp_notmem_0116) (nb060_wpp_notmem_0117 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_044) (nb060_alpha_dummy_046 x y) (nb060_wpp_notmem_0118) (nb060_wpp_notmem_0119 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_043) (nb060_alpha_dummy_045 x y) (nb060_wpp_notmem_0120) (nb060_wpp_notmem_0121 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_049) (nb060_alpha_dummy_050 x y) (nb060_wpp_notmem_0122) (nb060_wpp_notmem_0123 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_047) (nb060_alpha_dummy_048 x y) (nb060_wpp_notmem_0124) (nb060_wpp_notmem_0125 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0126) (nb060_wpp_notmem_0127 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0128) (nb060_wpp_notmem_0129 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0130) (nb060_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0020) (nb060_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0022) (nb060_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0024) (nb060_wpp_notmem_0025 x y z r a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb060_wpp_refl_0007 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0007 x y z r a)

theorem nb060_wpp_notmem_0132 : (nb060_alpha_dummy_059) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_059, fv_syn_c0] using (nb060_compact_fv_empty_0032)

theorem nb060_wpp_notmem_0133 (x : Var) (y : Var) : (nb060_alpha_dummy_062 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_062, fv_syn_c0] using (nb060_compact_fv_empty_0033 x y)

theorem nb060_wpp_notmem_0134 : (nb060_alpha_dummy_058) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_058, fv_syn_c0] using (nb060_compact_fv_empty_0034)

theorem nb060_wpp_notmem_0135 (x : Var) (y : Var) : (nb060_alpha_dummy_061 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_061, fv_syn_c0] using (nb060_compact_fv_empty_0035 x y)

theorem nb060_wpp_notmem_0136 : (nb060_alpha_dummy_057) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_057, fv_syn_c0] using (nb060_compact_fv_empty_0036)

theorem nb060_wpp_notmem_0137 (x : Var) (y : Var) : (nb060_alpha_dummy_060 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_060, fv_syn_c0] using (nb060_compact_fv_empty_0037 x y)

theorem nb060_wpp_notmem_0138 : (nb060_alpha_dummy_055) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_055, fv_syn_c0] using (nb060_compact_fv_empty_0038)

theorem nb060_wpp_notmem_0139 (x : Var) (y : Var) : (nb060_alpha_dummy_056 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_056, fv_syn_c0] using (nb060_compact_fv_empty_0039 x y)

theorem nb060_wpp_notmem_0140 : (nb060_alpha_dummy_051) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_051, fv_syn_c0] using (nb060_compact_fv_empty_0040)

theorem nb060_wpp_notmem_0141 (x : Var) (y : Var) : (nb060_alpha_dummy_053 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_053, fv_syn_c0] using (nb060_compact_fv_empty_0041 x y)

theorem nb060_wpp_notmem_0142 : (nb060_alpha_dummy_052) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_052, fv_syn_c0] using (nb060_compact_fv_empty_0042)

theorem nb060_wpp_notmem_0143 (x : Var) (y : Var) : (nb060_alpha_dummy_054 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_054, fv_syn_c0] using (nb060_compact_fv_empty_0043 x y)

theorem nb060_wpp_notmem_0144 : (nb060_alpha_dummy_044) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_044, fv_syn_c0] using (nb060_compact_fv_empty_0044)

theorem nb060_wpp_notmem_0145 (x : Var) (y : Var) : (nb060_alpha_dummy_046 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_046, fv_syn_c0] using (nb060_compact_fv_empty_0045 x y)

theorem nb060_wpp_notmem_0146 : (nb060_alpha_dummy_043) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_043, fv_syn_c0] using (nb060_compact_fv_empty_0046)

theorem nb060_wpp_notmem_0147 (x : Var) (y : Var) : (nb060_alpha_dummy_045 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_045, fv_syn_c0] using (nb060_compact_fv_empty_0047 x y)

theorem nb060_wpp_notmem_0148 : (nb060_alpha_dummy_049) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_049, fv_syn_c0] using (nb060_compact_fv_empty_0048)

theorem nb060_wpp_notmem_0149 (x : Var) (y : Var) : (nb060_alpha_dummy_050 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_050, fv_syn_c0] using (nb060_compact_fv_empty_0049 x y)

theorem nb060_wpp_notmem_0150 : (nb060_alpha_dummy_047) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_047, fv_syn_c0] using (nb060_compact_fv_empty_0050)

theorem nb060_wpp_notmem_0151 (x : Var) (y : Var) : (nb060_alpha_dummy_048 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_048, fv_syn_c0] using (nb060_compact_fv_empty_0051 x y)

theorem nb060_wpp_notmem_0152 : (nb060_alpha_dummy_004) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_004, fv_syn_c0] using (nb060_compact_fv_empty_0052)

theorem nb060_wpp_notmem_0153 (z : Var) : z ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb060_compact_fv_empty_0053 z)

theorem nb060_wpp_notmem_0154 : (nb060_alpha_dummy_003) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_003, fv_syn_c0] using (nb060_compact_fv_empty_0054)

theorem nb060_wpp_notmem_0155 (y : Var) : y ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb060_compact_fv_empty_0055 y)

theorem nb060_wpp_notmem_0156 : (nb060_alpha_dummy_002) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_002, fv_syn_c0] using (nb060_compact_fv_empty_0056)

theorem nb060_wpp_notmem_0157 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb060_compact_fv_empty_0057 x)

theorem nb060_compact_envfresh_0008 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_059) (nb060_alpha_dummy_062 x y) (nb060_wpp_notmem_0132) (nb060_wpp_notmem_0133 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_058) (nb060_alpha_dummy_061 x y) (nb060_wpp_notmem_0134) (nb060_wpp_notmem_0135 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_057) (nb060_alpha_dummy_060 x y) (nb060_wpp_notmem_0136) (nb060_wpp_notmem_0137 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_055) (nb060_alpha_dummy_056 x y) (nb060_wpp_notmem_0138) (nb060_wpp_notmem_0139 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_051) (nb060_alpha_dummy_053 x y) (nb060_wpp_notmem_0140) (nb060_wpp_notmem_0141 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_052) (nb060_alpha_dummy_054 x y) (nb060_wpp_notmem_0142) (nb060_wpp_notmem_0143 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_044) (nb060_alpha_dummy_046 x y) (nb060_wpp_notmem_0144) (nb060_wpp_notmem_0145 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_043) (nb060_alpha_dummy_045 x y) (nb060_wpp_notmem_0146) (nb060_wpp_notmem_0147 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_049) (nb060_alpha_dummy_050 x y) (nb060_wpp_notmem_0148) (nb060_wpp_notmem_0149 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_047) (nb060_alpha_dummy_048 x y) (nb060_wpp_notmem_0150) (nb060_wpp_notmem_0151 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0152) (nb060_wpp_notmem_0153 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0154) (nb060_wpp_notmem_0155 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0156) (nb060_wpp_notmem_0157 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0046) (nb060_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0048) (nb060_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0050) (nb060_wpp_notmem_0051 x y z r a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb060_wpp_refl_0008 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0008 x y z r a)

noncomputable def nb060_split_alpha_0005 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_057)) (syn_cun (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_060 x y)) (syn_cun (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_c0) (nb060_wpp_refl_0008 x y z r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb060_wpp_notmem_0158 : (nb060_alpha_dummy_055) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_055, fv_syn_cnnc] using (nb060_compact_fv_empty_0038)

theorem nb060_wpp_notmem_0159 (x : Var) (y : Var) : (nb060_alpha_dummy_056 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_056, fv_syn_cnnc] using (nb060_compact_fv_empty_0039 x y)

theorem nb060_wpp_notmem_0160 : (nb060_alpha_dummy_051) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_051, fv_syn_cnnc] using (nb060_compact_fv_empty_0040)

theorem nb060_wpp_notmem_0161 (x : Var) (y : Var) : (nb060_alpha_dummy_053 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_053, fv_syn_cnnc] using (nb060_compact_fv_empty_0041 x y)

theorem nb060_wpp_notmem_0162 : (nb060_alpha_dummy_052) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_052, fv_syn_cnnc] using (nb060_compact_fv_empty_0042)

theorem nb060_wpp_notmem_0163 (x : Var) (y : Var) : (nb060_alpha_dummy_054 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_054, fv_syn_cnnc] using (nb060_compact_fv_empty_0043 x y)

theorem nb060_wpp_notmem_0164 : (nb060_alpha_dummy_044) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_044, fv_syn_cnnc] using (nb060_compact_fv_empty_0044)

theorem nb060_wpp_notmem_0165 (x : Var) (y : Var) : (nb060_alpha_dummy_046 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_046, fv_syn_cnnc] using (nb060_compact_fv_empty_0045 x y)

theorem nb060_wpp_notmem_0166 : (nb060_alpha_dummy_043) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_043, fv_syn_cnnc] using (nb060_compact_fv_empty_0046)

theorem nb060_wpp_notmem_0167 (x : Var) (y : Var) : (nb060_alpha_dummy_045 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_045, fv_syn_cnnc] using (nb060_compact_fv_empty_0047 x y)

theorem nb060_wpp_notmem_0168 : (nb060_alpha_dummy_049) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_049, fv_syn_cnnc] using (nb060_compact_fv_empty_0048)

theorem nb060_wpp_notmem_0169 (x : Var) (y : Var) : (nb060_alpha_dummy_050 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_050, fv_syn_cnnc] using (nb060_compact_fv_empty_0049 x y)

theorem nb060_wpp_notmem_0170 : (nb060_alpha_dummy_047) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_047, fv_syn_cnnc] using (nb060_compact_fv_empty_0050)

theorem nb060_wpp_notmem_0171 (x : Var) (y : Var) : (nb060_alpha_dummy_048 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_048, fv_syn_cnnc] using (nb060_compact_fv_empty_0051 x y)

theorem nb060_wpp_notmem_0172 : (nb060_alpha_dummy_004) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_004, fv_syn_cnnc] using (nb060_compact_fv_empty_0052)

theorem nb060_wpp_notmem_0173 (z : Var) : z ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb060_compact_fv_empty_0053 z)

theorem nb060_wpp_notmem_0174 : (nb060_alpha_dummy_003) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_003, fv_syn_cnnc] using (nb060_compact_fv_empty_0054)

theorem nb060_wpp_notmem_0175 (y : Var) : y ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb060_compact_fv_empty_0055 y)

theorem nb060_wpp_notmem_0176 : (nb060_alpha_dummy_002) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_002, fv_syn_cnnc] using (nb060_compact_fv_empty_0056)

theorem nb060_wpp_notmem_0177 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb060_compact_fv_empty_0057 x)

theorem nb060_compact_envfresh_0009 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_055) (nb060_alpha_dummy_056 x y) (nb060_wpp_notmem_0158) (nb060_wpp_notmem_0159 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_051) (nb060_alpha_dummy_053 x y) (nb060_wpp_notmem_0160) (nb060_wpp_notmem_0161 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_052) (nb060_alpha_dummy_054 x y) (nb060_wpp_notmem_0162) (nb060_wpp_notmem_0163 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_044) (nb060_alpha_dummy_046 x y) (nb060_wpp_notmem_0164) (nb060_wpp_notmem_0165 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_043) (nb060_alpha_dummy_045 x y) (nb060_wpp_notmem_0166) (nb060_wpp_notmem_0167 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_049) (nb060_alpha_dummy_050 x y) (nb060_wpp_notmem_0168) (nb060_wpp_notmem_0169 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_047) (nb060_alpha_dummy_048 x y) (nb060_wpp_notmem_0170) (nb060_wpp_notmem_0171 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0172) (nb060_wpp_notmem_0173 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0174) (nb060_wpp_notmem_0175 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0176) (nb060_wpp_notmem_0177 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0066) (nb060_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0068) (nb060_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0070) (nb060_wpp_notmem_0071 x y z r a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb060_wpp_refl_0009 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0009 x y z r a)

noncomputable def nb060_split_alpha_0006 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) : TAlphaWff [((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_044)) (Class.cv (nb060_alpha_dummy_002))) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))) (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_046 x y)) (Class.cv x)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0046) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0047 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0043) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0045 x y) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_044))).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_046 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0053 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0053 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (nb060_wpp_refl_0007 x y z r a))) (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0005 x y z r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb060_wpp_refl_0009 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb060_wpp_refl_0009 x y z r a))))))))))))))))))))

theorem nb060_compact_fv_empty_0058 : (nb060_alpha_dummy_077) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0178 : (nb060_alpha_dummy_077) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_077, fv_syn_c1c] using (nb060_compact_fv_empty_0058)

theorem nb060_compact_fv_empty_0059 (x : Var) (y : Var) : (nb060_alpha_dummy_078 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0179 (x : Var) (y : Var) : (nb060_alpha_dummy_078 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_078, fv_syn_c1c] using (nb060_compact_fv_empty_0059 x y)

theorem nb060_compact_fv_empty_0060 : (nb060_alpha_dummy_075) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0180 : (nb060_alpha_dummy_075) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_075, fv_syn_c1c] using (nb060_compact_fv_empty_0060)

theorem nb060_compact_fv_empty_0061 (x : Var) (y : Var) : (nb060_alpha_dummy_076 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0181 (x : Var) (y : Var) : (nb060_alpha_dummy_076 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_076, fv_syn_c1c] using (nb060_compact_fv_empty_0061 x y)

theorem nb060_compact_fv_empty_0062 : (nb060_alpha_dummy_073) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0182 : (nb060_alpha_dummy_073) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_073, fv_syn_c1c] using (nb060_compact_fv_empty_0062)

theorem nb060_compact_fv_empty_0063 (x : Var) (y : Var) : (nb060_alpha_dummy_074 x y) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0183 (x : Var) (y : Var) : (nb060_alpha_dummy_074 x y) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_074, fv_syn_c1c] using (nb060_compact_fv_empty_0063 x y)

theorem nb060_compact_envfresh_0010 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_059) (nb060_alpha_dummy_062 x y) (nb060_wpp_notmem_0106) (nb060_wpp_notmem_0107 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_058) (nb060_alpha_dummy_061 x y) (nb060_wpp_notmem_0108) (nb060_wpp_notmem_0109 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_057) (nb060_alpha_dummy_060 x y) (nb060_wpp_notmem_0110) (nb060_wpp_notmem_0111 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_055) (nb060_alpha_dummy_056 x y) (nb060_wpp_notmem_0112) (nb060_wpp_notmem_0113 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_051) (nb060_alpha_dummy_053 x y) (nb060_wpp_notmem_0114) (nb060_wpp_notmem_0115 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_052) (nb060_alpha_dummy_054 x y) (nb060_wpp_notmem_0116) (nb060_wpp_notmem_0117 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_077) (nb060_alpha_dummy_078 x y) (nb060_wpp_notmem_0178) (nb060_wpp_notmem_0179 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_075) (nb060_alpha_dummy_076 x y) (nb060_wpp_notmem_0180) (nb060_wpp_notmem_0181 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_044) (nb060_alpha_dummy_046 x y) (nb060_wpp_notmem_0118) (nb060_wpp_notmem_0119 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_043) (nb060_alpha_dummy_045 x y) (nb060_wpp_notmem_0120) (nb060_wpp_notmem_0121 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_073) (nb060_alpha_dummy_074 x y) (nb060_wpp_notmem_0182) (nb060_wpp_notmem_0183 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_047) (nb060_alpha_dummy_048 x y) (nb060_wpp_notmem_0124) (nb060_wpp_notmem_0125 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0126) (nb060_wpp_notmem_0127 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0128) (nb060_wpp_notmem_0129 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0130) (nb060_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0020) (nb060_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0022) (nb060_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0024) (nb060_wpp_notmem_0025 x y z r a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb060_wpp_refl_0010 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0010 x y z r a)

theorem nb060_wpp_notmem_0184 : (nb060_alpha_dummy_077) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_077, fv_syn_c0] using (nb060_compact_fv_empty_0058)

theorem nb060_wpp_notmem_0185 (x : Var) (y : Var) : (nb060_alpha_dummy_078 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_078, fv_syn_c0] using (nb060_compact_fv_empty_0059 x y)

theorem nb060_wpp_notmem_0186 : (nb060_alpha_dummy_075) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_075, fv_syn_c0] using (nb060_compact_fv_empty_0060)

theorem nb060_wpp_notmem_0187 (x : Var) (y : Var) : (nb060_alpha_dummy_076 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_076, fv_syn_c0] using (nb060_compact_fv_empty_0061 x y)

theorem nb060_wpp_notmem_0188 : (nb060_alpha_dummy_073) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_073, fv_syn_c0] using (nb060_compact_fv_empty_0062)

theorem nb060_wpp_notmem_0189 (x : Var) (y : Var) : (nb060_alpha_dummy_074 x y) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_074, fv_syn_c0] using (nb060_compact_fv_empty_0063 x y)

theorem nb060_compact_envfresh_0011 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_059) (nb060_alpha_dummy_062 x y) (nb060_wpp_notmem_0132) (nb060_wpp_notmem_0133 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_058) (nb060_alpha_dummy_061 x y) (nb060_wpp_notmem_0134) (nb060_wpp_notmem_0135 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_057) (nb060_alpha_dummy_060 x y) (nb060_wpp_notmem_0136) (nb060_wpp_notmem_0137 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_055) (nb060_alpha_dummy_056 x y) (nb060_wpp_notmem_0138) (nb060_wpp_notmem_0139 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_051) (nb060_alpha_dummy_053 x y) (nb060_wpp_notmem_0140) (nb060_wpp_notmem_0141 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_052) (nb060_alpha_dummy_054 x y) (nb060_wpp_notmem_0142) (nb060_wpp_notmem_0143 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_077) (nb060_alpha_dummy_078 x y) (nb060_wpp_notmem_0184) (nb060_wpp_notmem_0185 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_075) (nb060_alpha_dummy_076 x y) (nb060_wpp_notmem_0186) (nb060_wpp_notmem_0187 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_044) (nb060_alpha_dummy_046 x y) (nb060_wpp_notmem_0144) (nb060_wpp_notmem_0145 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_043) (nb060_alpha_dummy_045 x y) (nb060_wpp_notmem_0146) (nb060_wpp_notmem_0147 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_073) (nb060_alpha_dummy_074 x y) (nb060_wpp_notmem_0188) (nb060_wpp_notmem_0189 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_047) (nb060_alpha_dummy_048 x y) (nb060_wpp_notmem_0150) (nb060_wpp_notmem_0151 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0152) (nb060_wpp_notmem_0153 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0154) (nb060_wpp_notmem_0155 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0156) (nb060_wpp_notmem_0157 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0046) (nb060_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0048) (nb060_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0050) (nb060_wpp_notmem_0051 x y z r a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb060_wpp_refl_0011 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0011 x y z r a)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
