import NAR4C060C001Part006

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

noncomputable def nb060_split_alpha_0007 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_057)) (syn_cun (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_060 x y)) (syn_cun (Class.cv (nb060_alpha_dummy_061 x y)) (Class.cv (nb060_alpha_dummy_062 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_c0) (nb060_wpp_refl_0011 x y z r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb060_wpp_notmem_0190 : (nb060_alpha_dummy_077) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_077, fv_syn_cnnc] using (nb060_compact_fv_empty_0058)

theorem nb060_wpp_notmem_0191 (x : Var) (y : Var) : (nb060_alpha_dummy_078 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_078, fv_syn_cnnc] using (nb060_compact_fv_empty_0059 x y)

theorem nb060_wpp_notmem_0192 : (nb060_alpha_dummy_075) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_075, fv_syn_cnnc] using (nb060_compact_fv_empty_0060)

theorem nb060_wpp_notmem_0193 (x : Var) (y : Var) : (nb060_alpha_dummy_076 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_076, fv_syn_cnnc] using (nb060_compact_fv_empty_0061 x y)

theorem nb060_wpp_notmem_0194 : (nb060_alpha_dummy_073) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_073, fv_syn_cnnc] using (nb060_compact_fv_empty_0062)

theorem nb060_wpp_notmem_0195 (x : Var) (y : Var) : (nb060_alpha_dummy_074 x y) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_074, fv_syn_cnnc] using (nb060_compact_fv_empty_0063 x y)

theorem nb060_compact_envfresh_0012 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_055) (nb060_alpha_dummy_056 x y) (nb060_wpp_notmem_0158) (nb060_wpp_notmem_0159 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_051) (nb060_alpha_dummy_053 x y) (nb060_wpp_notmem_0160) (nb060_wpp_notmem_0161 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_052) (nb060_alpha_dummy_054 x y) (nb060_wpp_notmem_0162) (nb060_wpp_notmem_0163 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_077) (nb060_alpha_dummy_078 x y) (nb060_wpp_notmem_0190) (nb060_wpp_notmem_0191 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_075) (nb060_alpha_dummy_076 x y) (nb060_wpp_notmem_0192) (nb060_wpp_notmem_0193 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_044) (nb060_alpha_dummy_046 x y) (nb060_wpp_notmem_0164) (nb060_wpp_notmem_0165 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_043) (nb060_alpha_dummy_045 x y) (nb060_wpp_notmem_0166) (nb060_wpp_notmem_0167 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_073) (nb060_alpha_dummy_074 x y) (nb060_wpp_notmem_0194) (nb060_wpp_notmem_0195 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_047) (nb060_alpha_dummy_048 x y) (nb060_wpp_notmem_0170) (nb060_wpp_notmem_0171 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0172) (nb060_wpp_notmem_0173 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0174) (nb060_wpp_notmem_0175 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0176) (nb060_wpp_notmem_0177 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0066) (nb060_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0068) (nb060_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0070) (nb060_wpp_notmem_0071 x y z r a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb060_wpp_refl_0012 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0012 x y z r a)

noncomputable def nb060_split_alpha_0008 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (Class.cv (nb060_alpha_dummy_044))) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_052)) (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc)) (syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c)) (Class.cv (nb060_alpha_dummy_051)))))) (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (Class.cv (nb060_alpha_dummy_046 x y))) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_054 x y)) (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc)) (syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c)) (Class.cv (nb060_alpha_dummy_053 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0078) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0079 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0076) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0077 x y) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_044))).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_046 x y))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0052) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0053 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0052) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0053 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)), ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (nb060_wpp_refl_0010 x y z r a))) (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0007 x y z r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb060_wpp_refl_0012 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)), ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)), ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb060_wpp_refl_0012 x y z r a))))))))))))

theorem nb060_wpp_notmem_0196 : (nb060_alpha_dummy_075) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_075, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0060)

theorem nb060_wpp_notmem_0197 (x : Var) (y : Var) : (nb060_alpha_dummy_076 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_076, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0061 x y)

theorem nb060_wpp_notmem_0198 : (nb060_alpha_dummy_044) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0044)

theorem nb060_wpp_notmem_0199 (x : Var) (y : Var) : (nb060_alpha_dummy_046 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_046, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0045 x y)

theorem nb060_wpp_notmem_0200 : (nb060_alpha_dummy_043) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_043, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0046)

theorem nb060_wpp_notmem_0201 (x : Var) (y : Var) : (nb060_alpha_dummy_045 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_045, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0047 x y)

theorem nb060_wpp_notmem_0202 : (nb060_alpha_dummy_073) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_073, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0062)

theorem nb060_wpp_notmem_0203 (x : Var) (y : Var) : (nb060_alpha_dummy_074 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_074, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0063 x y)

theorem nb060_wpp_notmem_0204 : (nb060_alpha_dummy_047) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_047, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0050)

theorem nb060_wpp_notmem_0205 (x : Var) (y : Var) : (nb060_alpha_dummy_048 x y) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_048, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0051 x y)

theorem nb060_wpp_notmem_0206 : (nb060_alpha_dummy_004) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_004, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0052)

theorem nb060_wpp_notmem_0207 (z : Var) : z ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0053 z)

theorem nb060_wpp_notmem_0208 : (nb060_alpha_dummy_003) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_003, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0054)

theorem nb060_wpp_notmem_0209 (y : Var) : y ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0055 y)

theorem nb060_wpp_notmem_0210 : (nb060_alpha_dummy_002) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_002, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0056)

theorem nb060_wpp_notmem_0211 (x : Var) : x ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0057 x)

theorem nb060_compact_envfresh_0013 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_075) (nb060_alpha_dummy_076 x y) (nb060_wpp_notmem_0196) (nb060_wpp_notmem_0197 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_044) (nb060_alpha_dummy_046 x y) (nb060_wpp_notmem_0198) (nb060_wpp_notmem_0199 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_043) (nb060_alpha_dummy_045 x y) (nb060_wpp_notmem_0200) (nb060_wpp_notmem_0201 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_073) (nb060_alpha_dummy_074 x y) (nb060_wpp_notmem_0202) (nb060_wpp_notmem_0203 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_047) (nb060_alpha_dummy_048 x y) (nb060_wpp_notmem_0204) (nb060_wpp_notmem_0205 x y) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0206) (nb060_wpp_notmem_0207 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0208) (nb060_wpp_notmem_0209 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0210) (nb060_wpp_notmem_0211 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0100) (nb060_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0102) (nb060_wpp_notmem_0103 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0104) (nb060_wpp_notmem_0105 x y z r a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))

noncomputable def nb060_wpp_refl_0013 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0013 x y z r a)

noncomputable def nb060_split_alpha_0009 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) (dv_y_z : y ≠ z) : TAlphaWff [((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_073)) (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb060_alpha_dummy_073)) (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_074 x y)) (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb060_alpha_dummy_074 x y)) (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0075 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0071) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0073 x y) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0008 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0008 x y z r a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb060_wpp_refl_0013 x y z r a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0074) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0075 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0071) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0073 x y) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0008 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0008 x y z r a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)), ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)), ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)), ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb060_wpp_refl_0013 x y z r a)))))))))))))))))))

theorem nb060_compact_fv_empty_0064 : (nb060_alpha_dummy_095) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0212 : (nb060_alpha_dummy_095) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_095, fv_syn_c1c] using (nb060_compact_fv_empty_0064)

theorem nb060_compact_fv_empty_0065 (y : Var) (z : Var) : (nb060_alpha_dummy_098 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0213 (y : Var) (z : Var) : (nb060_alpha_dummy_098 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_098, fv_syn_c1c] using (nb060_compact_fv_empty_0065 y z)

theorem nb060_compact_fv_empty_0066 : (nb060_alpha_dummy_094) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0214 : (nb060_alpha_dummy_094) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_094, fv_syn_c1c] using (nb060_compact_fv_empty_0066)

theorem nb060_compact_fv_empty_0067 (y : Var) (z : Var) : (nb060_alpha_dummy_097 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0215 (y : Var) (z : Var) : (nb060_alpha_dummy_097 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_097, fv_syn_c1c] using (nb060_compact_fv_empty_0067 y z)

theorem nb060_compact_fv_empty_0068 : (nb060_alpha_dummy_093) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0216 : (nb060_alpha_dummy_093) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_093, fv_syn_c1c] using (nb060_compact_fv_empty_0068)

theorem nb060_compact_fv_empty_0069 (y : Var) (z : Var) : (nb060_alpha_dummy_096 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0217 (y : Var) (z : Var) : (nb060_alpha_dummy_096 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_096, fv_syn_c1c] using (nb060_compact_fv_empty_0069 y z)

theorem nb060_compact_fv_empty_0070 : (nb060_alpha_dummy_091) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0218 : (nb060_alpha_dummy_091) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_091, fv_syn_c1c] using (nb060_compact_fv_empty_0070)

theorem nb060_compact_fv_empty_0071 (y : Var) (z : Var) : (nb060_alpha_dummy_092 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0219 (y : Var) (z : Var) : (nb060_alpha_dummy_092 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_092, fv_syn_c1c] using (nb060_compact_fv_empty_0071 y z)

theorem nb060_compact_fv_empty_0072 : (nb060_alpha_dummy_087) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0220 : (nb060_alpha_dummy_087) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_087, fv_syn_c1c] using (nb060_compact_fv_empty_0072)

theorem nb060_compact_fv_empty_0073 (y : Var) (z : Var) : (nb060_alpha_dummy_089 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0221 (y : Var) (z : Var) : (nb060_alpha_dummy_089 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_089, fv_syn_c1c] using (nb060_compact_fv_empty_0073 y z)

theorem nb060_compact_fv_empty_0074 : (nb060_alpha_dummy_088) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0222 : (nb060_alpha_dummy_088) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_088, fv_syn_c1c] using (nb060_compact_fv_empty_0074)

theorem nb060_compact_fv_empty_0075 (y : Var) (z : Var) : (nb060_alpha_dummy_090 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0223 (y : Var) (z : Var) : (nb060_alpha_dummy_090 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_090, fv_syn_c1c] using (nb060_compact_fv_empty_0075 y z)

theorem nb060_compact_fv_empty_0076 : (nb060_alpha_dummy_080) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0224 : (nb060_alpha_dummy_080) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_080, fv_syn_c1c] using (nb060_compact_fv_empty_0076)

theorem nb060_compact_fv_empty_0077 (y : Var) (z : Var) : (nb060_alpha_dummy_082 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0225 (y : Var) (z : Var) : (nb060_alpha_dummy_082 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_082, fv_syn_c1c] using (nb060_compact_fv_empty_0077 y z)

theorem nb060_compact_fv_empty_0078 : (nb060_alpha_dummy_079) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0226 : (nb060_alpha_dummy_079) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_079, fv_syn_c1c] using (nb060_compact_fv_empty_0078)

theorem nb060_compact_fv_empty_0079 (y : Var) (z : Var) : (nb060_alpha_dummy_081 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0227 (y : Var) (z : Var) : (nb060_alpha_dummy_081 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_081, fv_syn_c1c] using (nb060_compact_fv_empty_0079 y z)

theorem nb060_compact_fv_empty_0080 : (nb060_alpha_dummy_085) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0228 : (nb060_alpha_dummy_085) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_085, fv_syn_c1c] using (nb060_compact_fv_empty_0080)

theorem nb060_compact_fv_empty_0081 (y : Var) (z : Var) : (nb060_alpha_dummy_086 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0229 (y : Var) (z : Var) : (nb060_alpha_dummy_086 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_086, fv_syn_c1c] using (nb060_compact_fv_empty_0081 y z)

theorem nb060_compact_fv_empty_0082 : (nb060_alpha_dummy_083) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0230 : (nb060_alpha_dummy_083) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_083, fv_syn_c1c] using (nb060_compact_fv_empty_0082)

theorem nb060_compact_fv_empty_0083 (y : Var) (z : Var) : (nb060_alpha_dummy_084 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0231 (y : Var) (z : Var) : (nb060_alpha_dummy_084 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_084, fv_syn_c1c] using (nb060_compact_fv_empty_0083 y z)

theorem nb060_compact_envfresh_0014 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_095) (nb060_alpha_dummy_098 y z) (nb060_wpp_notmem_0212) (nb060_wpp_notmem_0213 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_094) (nb060_alpha_dummy_097 y z) (nb060_wpp_notmem_0214) (nb060_wpp_notmem_0215 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_093) (nb060_alpha_dummy_096 y z) (nb060_wpp_notmem_0216) (nb060_wpp_notmem_0217 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_091) (nb060_alpha_dummy_092 y z) (nb060_wpp_notmem_0218) (nb060_wpp_notmem_0219 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_087) (nb060_alpha_dummy_089 y z) (nb060_wpp_notmem_0220) (nb060_wpp_notmem_0221 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_088) (nb060_alpha_dummy_090 y z) (nb060_wpp_notmem_0222) (nb060_wpp_notmem_0223 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_080) (nb060_alpha_dummy_082 y z) (nb060_wpp_notmem_0224) (nb060_wpp_notmem_0225 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_079) (nb060_alpha_dummy_081 y z) (nb060_wpp_notmem_0226) (nb060_wpp_notmem_0227 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_085) (nb060_alpha_dummy_086 y z) (nb060_wpp_notmem_0228) (nb060_wpp_notmem_0229 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_083) (nb060_alpha_dummy_084 y z) (nb060_wpp_notmem_0230) (nb060_wpp_notmem_0231 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0126) (nb060_wpp_notmem_0127 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0128) (nb060_wpp_notmem_0129 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0130) (nb060_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0020) (nb060_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0022) (nb060_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0024) (nb060_wpp_notmem_0025 x y z r a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb060_wpp_refl_0014 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0014 x y z r a)

theorem nb060_wpp_notmem_0232 : (nb060_alpha_dummy_095) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_095, fv_syn_c0] using (nb060_compact_fv_empty_0064)

theorem nb060_wpp_notmem_0233 (y : Var) (z : Var) : (nb060_alpha_dummy_098 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_098, fv_syn_c0] using (nb060_compact_fv_empty_0065 y z)

theorem nb060_wpp_notmem_0234 : (nb060_alpha_dummy_094) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_094, fv_syn_c0] using (nb060_compact_fv_empty_0066)

theorem nb060_wpp_notmem_0235 (y : Var) (z : Var) : (nb060_alpha_dummy_097 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_097, fv_syn_c0] using (nb060_compact_fv_empty_0067 y z)

theorem nb060_wpp_notmem_0236 : (nb060_alpha_dummy_093) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_093, fv_syn_c0] using (nb060_compact_fv_empty_0068)

theorem nb060_wpp_notmem_0237 (y : Var) (z : Var) : (nb060_alpha_dummy_096 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_096, fv_syn_c0] using (nb060_compact_fv_empty_0069 y z)

theorem nb060_wpp_notmem_0238 : (nb060_alpha_dummy_091) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_091, fv_syn_c0] using (nb060_compact_fv_empty_0070)

theorem nb060_wpp_notmem_0239 (y : Var) (z : Var) : (nb060_alpha_dummy_092 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_092, fv_syn_c0] using (nb060_compact_fv_empty_0071 y z)

theorem nb060_wpp_notmem_0240 : (nb060_alpha_dummy_087) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_087, fv_syn_c0] using (nb060_compact_fv_empty_0072)

theorem nb060_wpp_notmem_0241 (y : Var) (z : Var) : (nb060_alpha_dummy_089 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_089, fv_syn_c0] using (nb060_compact_fv_empty_0073 y z)

theorem nb060_wpp_notmem_0242 : (nb060_alpha_dummy_088) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_088, fv_syn_c0] using (nb060_compact_fv_empty_0074)

theorem nb060_wpp_notmem_0243 (y : Var) (z : Var) : (nb060_alpha_dummy_090 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_090, fv_syn_c0] using (nb060_compact_fv_empty_0075 y z)

theorem nb060_wpp_notmem_0244 : (nb060_alpha_dummy_080) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_080, fv_syn_c0] using (nb060_compact_fv_empty_0076)

theorem nb060_wpp_notmem_0245 (y : Var) (z : Var) : (nb060_alpha_dummy_082 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_082, fv_syn_c0] using (nb060_compact_fv_empty_0077 y z)

theorem nb060_wpp_notmem_0246 : (nb060_alpha_dummy_079) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_079, fv_syn_c0] using (nb060_compact_fv_empty_0078)

theorem nb060_wpp_notmem_0247 (y : Var) (z : Var) : (nb060_alpha_dummy_081 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_081, fv_syn_c0] using (nb060_compact_fv_empty_0079 y z)

theorem nb060_wpp_notmem_0248 : (nb060_alpha_dummy_085) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_085, fv_syn_c0] using (nb060_compact_fv_empty_0080)

theorem nb060_wpp_notmem_0249 (y : Var) (z : Var) : (nb060_alpha_dummy_086 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_086, fv_syn_c0] using (nb060_compact_fv_empty_0081 y z)

theorem nb060_wpp_notmem_0250 : (nb060_alpha_dummy_083) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_083, fv_syn_c0] using (nb060_compact_fv_empty_0082)

theorem nb060_wpp_notmem_0251 (y : Var) (z : Var) : (nb060_alpha_dummy_084 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_084, fv_syn_c0] using (nb060_compact_fv_empty_0083 y z)

theorem nb060_compact_envfresh_0015 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_095) (nb060_alpha_dummy_098 y z) (nb060_wpp_notmem_0232) (nb060_wpp_notmem_0233 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_094) (nb060_alpha_dummy_097 y z) (nb060_wpp_notmem_0234) (nb060_wpp_notmem_0235 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_093) (nb060_alpha_dummy_096 y z) (nb060_wpp_notmem_0236) (nb060_wpp_notmem_0237 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_091) (nb060_alpha_dummy_092 y z) (nb060_wpp_notmem_0238) (nb060_wpp_notmem_0239 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_087) (nb060_alpha_dummy_089 y z) (nb060_wpp_notmem_0240) (nb060_wpp_notmem_0241 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_088) (nb060_alpha_dummy_090 y z) (nb060_wpp_notmem_0242) (nb060_wpp_notmem_0243 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_080) (nb060_alpha_dummy_082 y z) (nb060_wpp_notmem_0244) (nb060_wpp_notmem_0245 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_079) (nb060_alpha_dummy_081 y z) (nb060_wpp_notmem_0246) (nb060_wpp_notmem_0247 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_085) (nb060_alpha_dummy_086 y z) (nb060_wpp_notmem_0248) (nb060_wpp_notmem_0249 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_083) (nb060_alpha_dummy_084 y z) (nb060_wpp_notmem_0250) (nb060_wpp_notmem_0251 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0152) (nb060_wpp_notmem_0153 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0154) (nb060_wpp_notmem_0155 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0156) (nb060_wpp_notmem_0157 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0046) (nb060_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0048) (nb060_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0050) (nb060_wpp_notmem_0051 x y z r a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb060_wpp_refl_0015 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0015 x y z r a)

noncomputable def nb060_split_alpha_0010 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_093)) (syn_cun (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_096 y z)) (syn_cun (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_c0) (nb060_wpp_refl_0015 x y z r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb060_wpp_notmem_0252 : (nb060_alpha_dummy_091) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_091, fv_syn_cnnc] using (nb060_compact_fv_empty_0070)

theorem nb060_wpp_notmem_0253 (y : Var) (z : Var) : (nb060_alpha_dummy_092 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_092, fv_syn_cnnc] using (nb060_compact_fv_empty_0071 y z)

theorem nb060_wpp_notmem_0254 : (nb060_alpha_dummy_087) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_087, fv_syn_cnnc] using (nb060_compact_fv_empty_0072)

theorem nb060_wpp_notmem_0255 (y : Var) (z : Var) : (nb060_alpha_dummy_089 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_089, fv_syn_cnnc] using (nb060_compact_fv_empty_0073 y z)

theorem nb060_wpp_notmem_0256 : (nb060_alpha_dummy_088) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_088, fv_syn_cnnc] using (nb060_compact_fv_empty_0074)

theorem nb060_wpp_notmem_0257 (y : Var) (z : Var) : (nb060_alpha_dummy_090 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_090, fv_syn_cnnc] using (nb060_compact_fv_empty_0075 y z)

theorem nb060_wpp_notmem_0258 : (nb060_alpha_dummy_080) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_080, fv_syn_cnnc] using (nb060_compact_fv_empty_0076)

theorem nb060_wpp_notmem_0259 (y : Var) (z : Var) : (nb060_alpha_dummy_082 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_082, fv_syn_cnnc] using (nb060_compact_fv_empty_0077 y z)

theorem nb060_wpp_notmem_0260 : (nb060_alpha_dummy_079) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_079, fv_syn_cnnc] using (nb060_compact_fv_empty_0078)

theorem nb060_wpp_notmem_0261 (y : Var) (z : Var) : (nb060_alpha_dummy_081 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_081, fv_syn_cnnc] using (nb060_compact_fv_empty_0079 y z)

theorem nb060_wpp_notmem_0262 : (nb060_alpha_dummy_085) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_085, fv_syn_cnnc] using (nb060_compact_fv_empty_0080)

theorem nb060_wpp_notmem_0263 (y : Var) (z : Var) : (nb060_alpha_dummy_086 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_086, fv_syn_cnnc] using (nb060_compact_fv_empty_0081 y z)

theorem nb060_wpp_notmem_0264 : (nb060_alpha_dummy_083) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_083, fv_syn_cnnc] using (nb060_compact_fv_empty_0082)

theorem nb060_wpp_notmem_0265 (y : Var) (z : Var) : (nb060_alpha_dummy_084 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_084, fv_syn_cnnc] using (nb060_compact_fv_empty_0083 y z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
