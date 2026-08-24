import NAR4C090C001Part071

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

noncomputable def nb090_split_alpha_0050 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_507 A)) (syn_cop (Class.cv (nb090_alpha_dummy_503 A)) (Class.cv (nb090_alpha_dummy_504 A)))) (Wff.neg (syn_wbr (Class.cv (nb090_alpha_dummy_504 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_503 A))))) (Wff.imp (Wff.classEq (Class.cv (nb090_alpha_dummy_508 h)) (syn_cop (Class.cv (nb090_alpha_dummy_505 h)) (Class.cv (nb090_alpha_dummy_506 h)))) (Wff.neg (syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_505 h))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0514 A) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0515 h) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0512 A) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0513 h) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0042 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0548 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0549 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0545 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0547 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0043 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0153 v u A h))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0548 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0549 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0545 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0547 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0043 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0153 v u A h))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0044 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0586 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0587 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0583 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0585 h) 0)) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0045 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)), ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)), ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0160 v u A h))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0586 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0587 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0583 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0585 h) 0)) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0045 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)), ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)), ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0160 v u A h)))))))))))))))))))))))))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0124 A) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0125 h) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0122 A) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0123 h) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0046 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0158 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0159 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0155 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0157 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0047 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0167 v u A h))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0158 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0159 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0155 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0157 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0047 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0167 v u A h))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0048 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0196 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0197 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0193 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0195 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0049 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0174 v u A h))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0196 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0197 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0193 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0195 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_129 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_131 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb090_split_alpha_0049 v u A h))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_203 A), (nb090_alpha_dummy_204 h)), ((nb090_alpha_dummy_172 A), (nb090_alpha_dummy_174 h)), ((nb090_alpha_dummy_171 A), (nb090_alpha_dummy_173 h)), ((nb090_alpha_dummy_201 A), (nb090_alpha_dummy_202 h)), ((nb090_alpha_dummy_175 A), (nb090_alpha_dummy_176 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0174 v u A h)))))))))))))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0212 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0213 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0212 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0213 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0210 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0211 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0602 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0603 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0602 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0603 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0600 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0601 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0596 A) 2)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0598 h) 2)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0596 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0598 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0596 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0598 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0597 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0599 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0594 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0595 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0592 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0593 h) 0)) (TAlphaVar.here _ _ _))))))))))))))))))))))))))))

theorem nb090_compact_fv_empty_0436 (A : Class) : (nb090_alpha_dummy_597 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1502 (A : Class) : (nb090_alpha_dummy_597 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_597, fv_syn_c1c] using (nb090_compact_fv_empty_0436 A)

theorem nb090_compact_fv_empty_0437 (h : Var) : (nb090_alpha_dummy_600 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1503 (h : Var) : (nb090_alpha_dummy_600 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_600, fv_syn_c1c] using (nb090_compact_fv_empty_0437 h)

theorem nb090_compact_fv_empty_0438 (A : Class) : (nb090_alpha_dummy_596 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1504 (A : Class) : (nb090_alpha_dummy_596 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_596, fv_syn_c1c] using (nb090_compact_fv_empty_0438 A)

theorem nb090_compact_fv_empty_0439 (h : Var) : (nb090_alpha_dummy_599 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1505 (h : Var) : (nb090_alpha_dummy_599 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_599, fv_syn_c1c] using (nb090_compact_fv_empty_0439 h)

theorem nb090_compact_fv_empty_0440 (A : Class) : (nb090_alpha_dummy_595 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1506 (A : Class) : (nb090_alpha_dummy_595 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_595, fv_syn_c1c] using (nb090_compact_fv_empty_0440 A)

theorem nb090_compact_fv_empty_0441 (h : Var) : (nb090_alpha_dummy_598 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1507 (h : Var) : (nb090_alpha_dummy_598 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_598, fv_syn_c1c] using (nb090_compact_fv_empty_0441 h)

theorem nb090_compact_fv_empty_0442 (A : Class) : (nb090_alpha_dummy_593 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1508 (A : Class) : (nb090_alpha_dummy_593 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_593, fv_syn_c1c] using (nb090_compact_fv_empty_0442 A)

theorem nb090_compact_fv_empty_0443 (h : Var) : (nb090_alpha_dummy_594 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1509 (h : Var) : (nb090_alpha_dummy_594 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_594, fv_syn_c1c] using (nb090_compact_fv_empty_0443 h)

theorem nb090_compact_fv_empty_0444 (A : Class) : (nb090_alpha_dummy_589 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1510 (A : Class) : (nb090_alpha_dummy_589 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_589, fv_syn_c1c] using (nb090_compact_fv_empty_0444 A)

theorem nb090_compact_fv_empty_0445 (h : Var) : (nb090_alpha_dummy_591 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1511 (h : Var) : (nb090_alpha_dummy_591 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_591, fv_syn_c1c] using (nb090_compact_fv_empty_0445 h)

theorem nb090_compact_fv_empty_0446 (A : Class) : (nb090_alpha_dummy_590 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1512 (A : Class) : (nb090_alpha_dummy_590 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_590, fv_syn_c1c] using (nb090_compact_fv_empty_0446 A)

theorem nb090_compact_fv_empty_0447 (h : Var) : (nb090_alpha_dummy_592 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1513 (h : Var) : (nb090_alpha_dummy_592 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_592, fv_syn_c1c] using (nb090_compact_fv_empty_0447 h)

theorem nb090_compact_fv_empty_0448 (A : Class) : (nb090_alpha_dummy_582 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1514 (A : Class) : (nb090_alpha_dummy_582 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_582, fv_syn_c1c] using (nb090_compact_fv_empty_0448 A)

theorem nb090_compact_fv_empty_0449 (h : Var) : (nb090_alpha_dummy_584 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1515 (h : Var) : (nb090_alpha_dummy_584 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_584, fv_syn_c1c] using (nb090_compact_fv_empty_0449 h)

theorem nb090_compact_fv_empty_0450 (A : Class) : (nb090_alpha_dummy_581 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1516 (A : Class) : (nb090_alpha_dummy_581 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_581, fv_syn_c1c] using (nb090_compact_fv_empty_0450 A)

theorem nb090_compact_fv_empty_0451 (h : Var) : (nb090_alpha_dummy_583 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1517 (h : Var) : (nb090_alpha_dummy_583 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_583, fv_syn_c1c] using (nb090_compact_fv_empty_0451 h)

theorem nb090_compact_fv_empty_0452 (A : Class) : (nb090_alpha_dummy_587 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1518 (A : Class) : (nb090_alpha_dummy_587 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_587, fv_syn_c1c] using (nb090_compact_fv_empty_0452 A)

theorem nb090_compact_fv_empty_0453 (h : Var) : (nb090_alpha_dummy_588 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1519 (h : Var) : (nb090_alpha_dummy_588 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_588, fv_syn_c1c] using (nb090_compact_fv_empty_0453 h)

theorem nb090_compact_fv_empty_0454 (A : Class) : (nb090_alpha_dummy_585 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1520 (A : Class) : (nb090_alpha_dummy_585 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_585, fv_syn_c1c] using (nb090_compact_fv_empty_0454 A)

theorem nb090_compact_fv_empty_0455 (h : Var) : (nb090_alpha_dummy_586 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1521 (h : Var) : (nb090_alpha_dummy_586 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_586, fv_syn_c1c] using (nb090_compact_fv_empty_0455 h)

theorem nb090_compact_envfresh_0175 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A), (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)), ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)), ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)), ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_597 A) (nb090_alpha_dummy_600 h) (nb090_wpp_notmem_1502 A) (nb090_wpp_notmem_1503 h) (TEnvFresh.consFresh (nb090_alpha_dummy_596 A) (nb090_alpha_dummy_599 h) (nb090_wpp_notmem_1504 A) (nb090_wpp_notmem_1505 h) (TEnvFresh.consFresh (nb090_alpha_dummy_595 A) (nb090_alpha_dummy_598 h) (nb090_wpp_notmem_1506 A) (nb090_wpp_notmem_1507 h) (TEnvFresh.consFresh (nb090_alpha_dummy_593 A) (nb090_alpha_dummy_594 h) (nb090_wpp_notmem_1508 A) (nb090_wpp_notmem_1509 h) (TEnvFresh.consFresh (nb090_alpha_dummy_589 A) (nb090_alpha_dummy_591 h) (nb090_wpp_notmem_1510 A) (nb090_wpp_notmem_1511 h) (TEnvFresh.consFresh (nb090_alpha_dummy_590 A) (nb090_alpha_dummy_592 h) (nb090_wpp_notmem_1512 A) (nb090_wpp_notmem_1513 h) (TEnvFresh.consFresh (nb090_alpha_dummy_582 A) (nb090_alpha_dummy_584 h) (nb090_wpp_notmem_1514 A) (nb090_wpp_notmem_1515 h) (TEnvFresh.consFresh (nb090_alpha_dummy_581 A) (nb090_alpha_dummy_583 h) (nb090_wpp_notmem_1516 A) (nb090_wpp_notmem_1517 h) (TEnvFresh.consFresh (nb090_alpha_dummy_587 A) (nb090_alpha_dummy_588 h) (nb090_wpp_notmem_1518 A) (nb090_wpp_notmem_1519 h) (TEnvFresh.consFresh (nb090_alpha_dummy_585 A) (nb090_alpha_dummy_586 h) (nb090_wpp_notmem_1520 A) (nb090_wpp_notmem_1521 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1244 A) (nb090_wpp_notmem_1245 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1122 A) (nb090_wpp_notmem_1123 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1124 A) (nb090_wpp_notmem_1125 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1126 A) (nb090_wpp_notmem_1127 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1128 A) (nb090_wpp_notmem_1129 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1130 A) (nb090_wpp_notmem_1131 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb090_wpp_refl_0175 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A), (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)), ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)), ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)), ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0175 v u A h)

theorem nb090_wpp_notmem_1522 (A : Class) : (nb090_alpha_dummy_597 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_597, fv_syn_c0] using (nb090_compact_fv_empty_0436 A)

theorem nb090_wpp_notmem_1523 (h : Var) : (nb090_alpha_dummy_600 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_600, fv_syn_c0] using (nb090_compact_fv_empty_0437 h)

theorem nb090_wpp_notmem_1524 (A : Class) : (nb090_alpha_dummy_596 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_596, fv_syn_c0] using (nb090_compact_fv_empty_0438 A)

theorem nb090_wpp_notmem_1525 (h : Var) : (nb090_alpha_dummy_599 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_599, fv_syn_c0] using (nb090_compact_fv_empty_0439 h)

theorem nb090_wpp_notmem_1526 (A : Class) : (nb090_alpha_dummy_595 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_595, fv_syn_c0] using (nb090_compact_fv_empty_0440 A)

theorem nb090_wpp_notmem_1527 (h : Var) : (nb090_alpha_dummy_598 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_598, fv_syn_c0] using (nb090_compact_fv_empty_0441 h)

theorem nb090_wpp_notmem_1528 (A : Class) : (nb090_alpha_dummy_593 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_593, fv_syn_c0] using (nb090_compact_fv_empty_0442 A)

theorem nb090_wpp_notmem_1529 (h : Var) : (nb090_alpha_dummy_594 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_594, fv_syn_c0] using (nb090_compact_fv_empty_0443 h)

theorem nb090_wpp_notmem_1530 (A : Class) : (nb090_alpha_dummy_589 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_589, fv_syn_c0] using (nb090_compact_fv_empty_0444 A)

theorem nb090_wpp_notmem_1531 (h : Var) : (nb090_alpha_dummy_591 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_591, fv_syn_c0] using (nb090_compact_fv_empty_0445 h)

theorem nb090_wpp_notmem_1532 (A : Class) : (nb090_alpha_dummy_590 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_590, fv_syn_c0] using (nb090_compact_fv_empty_0446 A)

theorem nb090_wpp_notmem_1533 (h : Var) : (nb090_alpha_dummy_592 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_592, fv_syn_c0] using (nb090_compact_fv_empty_0447 h)

theorem nb090_wpp_notmem_1534 (A : Class) : (nb090_alpha_dummy_582 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_582, fv_syn_c0] using (nb090_compact_fv_empty_0448 A)

theorem nb090_wpp_notmem_1535 (h : Var) : (nb090_alpha_dummy_584 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_584, fv_syn_c0] using (nb090_compact_fv_empty_0449 h)

theorem nb090_wpp_notmem_1536 (A : Class) : (nb090_alpha_dummy_581 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_581, fv_syn_c0] using (nb090_compact_fv_empty_0450 A)

theorem nb090_wpp_notmem_1537 (h : Var) : (nb090_alpha_dummy_583 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_583, fv_syn_c0] using (nb090_compact_fv_empty_0451 h)

theorem nb090_wpp_notmem_1538 (A : Class) : (nb090_alpha_dummy_587 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_587, fv_syn_c0] using (nb090_compact_fv_empty_0452 A)

theorem nb090_wpp_notmem_1539 (h : Var) : (nb090_alpha_dummy_588 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_588, fv_syn_c0] using (nb090_compact_fv_empty_0453 h)

theorem nb090_wpp_notmem_1540 (A : Class) : (nb090_alpha_dummy_585 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_585, fv_syn_c0] using (nb090_compact_fv_empty_0454 A)

theorem nb090_wpp_notmem_1541 (h : Var) : (nb090_alpha_dummy_586 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_586, fv_syn_c0] using (nb090_compact_fv_empty_0455 h)

theorem nb090_compact_envfresh_0176 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A), (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)), ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)), ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)), ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_597 A) (nb090_alpha_dummy_600 h) (nb090_wpp_notmem_1522 A) (nb090_wpp_notmem_1523 h) (TEnvFresh.consFresh (nb090_alpha_dummy_596 A) (nb090_alpha_dummy_599 h) (nb090_wpp_notmem_1524 A) (nb090_wpp_notmem_1525 h) (TEnvFresh.consFresh (nb090_alpha_dummy_595 A) (nb090_alpha_dummy_598 h) (nb090_wpp_notmem_1526 A) (nb090_wpp_notmem_1527 h) (TEnvFresh.consFresh (nb090_alpha_dummy_593 A) (nb090_alpha_dummy_594 h) (nb090_wpp_notmem_1528 A) (nb090_wpp_notmem_1529 h) (TEnvFresh.consFresh (nb090_alpha_dummy_589 A) (nb090_alpha_dummy_591 h) (nb090_wpp_notmem_1530 A) (nb090_wpp_notmem_1531 h) (TEnvFresh.consFresh (nb090_alpha_dummy_590 A) (nb090_alpha_dummy_592 h) (nb090_wpp_notmem_1532 A) (nb090_wpp_notmem_1533 h) (TEnvFresh.consFresh (nb090_alpha_dummy_582 A) (nb090_alpha_dummy_584 h) (nb090_wpp_notmem_1534 A) (nb090_wpp_notmem_1535 h) (TEnvFresh.consFresh (nb090_alpha_dummy_581 A) (nb090_alpha_dummy_583 h) (nb090_wpp_notmem_1536 A) (nb090_wpp_notmem_1537 h) (TEnvFresh.consFresh (nb090_alpha_dummy_587 A) (nb090_alpha_dummy_588 h) (nb090_wpp_notmem_1538 A) (nb090_wpp_notmem_1539 h) (TEnvFresh.consFresh (nb090_alpha_dummy_585 A) (nb090_alpha_dummy_586 h) (nb090_wpp_notmem_1540 A) (nb090_wpp_notmem_1541 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1266 A) (nb090_wpp_notmem_1267 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1152 A) (nb090_wpp_notmem_1153 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1154 A) (nb090_wpp_notmem_1155 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1156 A) (nb090_wpp_notmem_1157 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1158 A) (nb090_wpp_notmem_1159 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1160 A) (nb090_wpp_notmem_1161 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb090_wpp_refl_0176 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_597 A), (nb090_alpha_dummy_600 h)), ((nb090_alpha_dummy_596 A), (nb090_alpha_dummy_599 h)), ((nb090_alpha_dummy_595 A), (nb090_alpha_dummy_598 h)), ((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)), ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)), ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0176 v u A h)

theorem nb090_wpp_notmem_1542 (A : Class) : (nb090_alpha_dummy_593 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_593, fv_syn_cnnc] using (nb090_compact_fv_empty_0442 A)

theorem nb090_wpp_notmem_1543 (h : Var) : (nb090_alpha_dummy_594 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_594, fv_syn_cnnc] using (nb090_compact_fv_empty_0443 h)

theorem nb090_wpp_notmem_1544 (A : Class) : (nb090_alpha_dummy_589 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_589, fv_syn_cnnc] using (nb090_compact_fv_empty_0444 A)

theorem nb090_wpp_notmem_1545 (h : Var) : (nb090_alpha_dummy_591 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_591, fv_syn_cnnc] using (nb090_compact_fv_empty_0445 h)

theorem nb090_wpp_notmem_1546 (A : Class) : (nb090_alpha_dummy_590 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_590, fv_syn_cnnc] using (nb090_compact_fv_empty_0446 A)

theorem nb090_wpp_notmem_1547 (h : Var) : (nb090_alpha_dummy_592 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_592, fv_syn_cnnc] using (nb090_compact_fv_empty_0447 h)

theorem nb090_wpp_notmem_1548 (A : Class) : (nb090_alpha_dummy_582 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_582, fv_syn_cnnc] using (nb090_compact_fv_empty_0448 A)

theorem nb090_wpp_notmem_1549 (h : Var) : (nb090_alpha_dummy_584 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_584, fv_syn_cnnc] using (nb090_compact_fv_empty_0449 h)

theorem nb090_wpp_notmem_1550 (A : Class) : (nb090_alpha_dummy_581 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_581, fv_syn_cnnc] using (nb090_compact_fv_empty_0450 A)

theorem nb090_wpp_notmem_1551 (h : Var) : (nb090_alpha_dummy_583 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_583, fv_syn_cnnc] using (nb090_compact_fv_empty_0451 h)

theorem nb090_wpp_notmem_1552 (A : Class) : (nb090_alpha_dummy_587 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_587, fv_syn_cnnc] using (nb090_compact_fv_empty_0452 A)

theorem nb090_wpp_notmem_1553 (h : Var) : (nb090_alpha_dummy_588 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_588, fv_syn_cnnc] using (nb090_compact_fv_empty_0453 h)

theorem nb090_wpp_notmem_1554 (A : Class) : (nb090_alpha_dummy_585 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_585, fv_syn_cnnc] using (nb090_compact_fv_empty_0454 A)

theorem nb090_wpp_notmem_1555 (h : Var) : (nb090_alpha_dummy_586 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_586, fv_syn_cnnc] using (nb090_compact_fv_empty_0455 h)

theorem nb090_compact_envfresh_0177 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)), ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)), ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_593 A) (nb090_alpha_dummy_594 h) (nb090_wpp_notmem_1542 A) (nb090_wpp_notmem_1543 h) (TEnvFresh.consFresh (nb090_alpha_dummy_589 A) (nb090_alpha_dummy_591 h) (nb090_wpp_notmem_1544 A) (nb090_wpp_notmem_1545 h) (TEnvFresh.consFresh (nb090_alpha_dummy_590 A) (nb090_alpha_dummy_592 h) (nb090_wpp_notmem_1546 A) (nb090_wpp_notmem_1547 h) (TEnvFresh.consFresh (nb090_alpha_dummy_582 A) (nb090_alpha_dummy_584 h) (nb090_wpp_notmem_1548 A) (nb090_wpp_notmem_1549 h) (TEnvFresh.consFresh (nb090_alpha_dummy_581 A) (nb090_alpha_dummy_583 h) (nb090_wpp_notmem_1550 A) (nb090_wpp_notmem_1551 h) (TEnvFresh.consFresh (nb090_alpha_dummy_587 A) (nb090_alpha_dummy_588 h) (nb090_wpp_notmem_1552 A) (nb090_wpp_notmem_1553 h) (TEnvFresh.consFresh (nb090_alpha_dummy_585 A) (nb090_alpha_dummy_586 h) (nb090_wpp_notmem_1554 A) (nb090_wpp_notmem_1555 h) (TEnvFresh.consFresh (nb090_alpha_dummy_425 A) (nb090_alpha_dummy_428 h) (nb090_wpp_notmem_1282 A) (nb090_wpp_notmem_1283 h) (TEnvFresh.consFresh (nb090_alpha_dummy_424 A) (nb090_alpha_dummy_427 h) (nb090_wpp_notmem_1176 A) (nb090_wpp_notmem_1177 h) (TEnvFresh.consFresh (nb090_alpha_dummy_423 A) (nb090_alpha_dummy_426 h) (nb090_wpp_notmem_1178 A) (nb090_wpp_notmem_1179 h) (TEnvFresh.consFresh (nb090_alpha_dummy_429 A) (nb090_alpha_dummy_430 h) (nb090_wpp_notmem_1180 A) (nb090_wpp_notmem_1181 h) (TEnvFresh.consFresh (nb090_alpha_dummy_421 A) (nb090_alpha_dummy_422 h) (nb090_wpp_notmem_1182 A) (nb090_wpp_notmem_1183 h) (TEnvFresh.consFresh (nb090_alpha_dummy_419 A) (nb090_alpha_dummy_420 h) (nb090_wpp_notmem_1184 A) (nb090_wpp_notmem_1185 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb090_wpp_refl_0177 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_593 A), (nb090_alpha_dummy_594 h)), ((nb090_alpha_dummy_589 A), (nb090_alpha_dummy_591 h)), ((nb090_alpha_dummy_590 A), (nb090_alpha_dummy_592 h)), ((nb090_alpha_dummy_582 A), (nb090_alpha_dummy_584 h)), ((nb090_alpha_dummy_581 A), (nb090_alpha_dummy_583 h)), ((nb090_alpha_dummy_587 A), (nb090_alpha_dummy_588 h)), ((nb090_alpha_dummy_585 A), (nb090_alpha_dummy_586 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0177 v u A h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
