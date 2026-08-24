import NAR4C078C001Part091

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

noncomputable def nb078_split_alpha_0065 (x : Var) (y : Var) (g : Var) : TAlphaWff [((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.classMem (Class.cv (nb078_alpha_dummy_645)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_614))))) (Wff.classMem (Class.cv (nb078_alpha_dummy_646 g)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0636) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0637 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0636) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0637 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0666) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0667 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0664) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0665 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_614))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_616 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0640) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0641 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0640) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0641 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0638) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0639 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628), (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)), ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0220 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0644) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0645 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0642) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0643 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0648) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0649 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0646) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0647 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0644) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0645 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0642) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0643 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0648) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0649 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0646) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0647 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628), (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)), ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0221 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0652) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0653 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0650) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0651 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0652) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0653 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0650) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0651 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0656) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0657 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0654) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0655 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0656) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0657 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0654) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0655 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0638) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0639 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0222 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0638) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0639 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0638) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0639 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0222 x y g)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0636) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0637 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0636) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0637 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0666) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0667 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0664) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0665 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_614))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_616 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0640) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0641 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0640) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0641 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0638) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0639 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628), (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)), ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0220 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0644) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0645 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0642) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0643 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0648) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0649 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0646) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0647 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0644) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0645 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0642) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0643 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0648) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0649 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0646) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0647 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628), (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)), ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0221 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0652) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0653 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0650) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0651 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0652) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0653 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0650) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0651 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0656) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0657 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0654) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0655 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0656) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0657 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0654) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0655 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0638) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0639 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0222 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0638) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0639 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0638) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0639 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)), ((nb078_alpha_dummy_647), (nb078_alpha_dummy_648 g)), ((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0222 x y g))))))))))))))))))))))))

theorem nb078_wpp_notmem_1648 : (nb078_alpha_dummy_645) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_645, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0488)

theorem nb078_wpp_notmem_1649 (g : Var) : (nb078_alpha_dummy_646 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_646, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0489 g)

theorem nb078_wpp_notmem_1650 : (nb078_alpha_dummy_614) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_614, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0476)

theorem nb078_wpp_notmem_1651 (g : Var) : (nb078_alpha_dummy_616 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_616, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0477 g)

theorem nb078_wpp_notmem_1652 : (nb078_alpha_dummy_613) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_613, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0478)

theorem nb078_wpp_notmem_1653 (g : Var) : (nb078_alpha_dummy_615 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_615, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0479 g)

theorem nb078_wpp_notmem_1654 : (nb078_alpha_dummy_643) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_643, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0490)

theorem nb078_wpp_notmem_1655 (g : Var) : (nb078_alpha_dummy_644 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_644, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0491 g)

theorem nb078_wpp_notmem_1656 : (nb078_alpha_dummy_617) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_617, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0482)

theorem nb078_wpp_notmem_1657 (g : Var) : (nb078_alpha_dummy_618 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_618, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0483 g)

theorem nb078_wpp_notmem_1658 : (nb078_alpha_dummy_571) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_571, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0484)

theorem nb078_wpp_notmem_1659 (g : Var) : (nb078_alpha_dummy_574 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_574, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0485 g)

theorem nb078_compact_envfresh_0223 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_645) (nb078_alpha_dummy_646 g) (nb078_wpp_notmem_1648) (nb078_wpp_notmem_1649 g) (TEnvFresh.consFresh (nb078_alpha_dummy_614) (nb078_alpha_dummy_616 g) (nb078_wpp_notmem_1650) (nb078_wpp_notmem_1651 g) (TEnvFresh.consFresh (nb078_alpha_dummy_613) (nb078_alpha_dummy_615 g) (nb078_wpp_notmem_1652) (nb078_wpp_notmem_1653 g) (TEnvFresh.consFresh (nb078_alpha_dummy_643) (nb078_alpha_dummy_644 g) (nb078_wpp_notmem_1654) (nb078_wpp_notmem_1655 g) (TEnvFresh.consFresh (nb078_alpha_dummy_617) (nb078_alpha_dummy_618 g) (nb078_wpp_notmem_1656) (nb078_wpp_notmem_1657 g) (TEnvFresh.consFresh (nb078_alpha_dummy_571) (nb078_alpha_dummy_574 g) (nb078_wpp_notmem_1658) (nb078_wpp_notmem_1659 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1560) (nb078_wpp_notmem_1561 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1562) (nb078_wpp_notmem_1563 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1564) (nb078_wpp_notmem_1565 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1566) (nb078_wpp_notmem_1567 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1568) (nb078_wpp_notmem_1569 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0854) (nb078_wpp_notmem_0855 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb078_wpp_refl_0223 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0223 x y g)

theorem nb078_compact_fv_empty_0492 : (nb078_alpha_dummy_671) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1660 : (nb078_alpha_dummy_671) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_671, fv_syn_c1c] using (nb078_compact_fv_empty_0492)

theorem nb078_compact_fv_empty_0493 (g : Var) : (nb078_alpha_dummy_674 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1661 (g : Var) : (nb078_alpha_dummy_674 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_674, fv_syn_c1c] using (nb078_compact_fv_empty_0493 g)

theorem nb078_compact_fv_empty_0494 : (nb078_alpha_dummy_670) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1662 : (nb078_alpha_dummy_670) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_670, fv_syn_c1c] using (nb078_compact_fv_empty_0494)

theorem nb078_compact_fv_empty_0495 (g : Var) : (nb078_alpha_dummy_673 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1663 (g : Var) : (nb078_alpha_dummy_673 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_673, fv_syn_c1c] using (nb078_compact_fv_empty_0495 g)

theorem nb078_compact_fv_empty_0496 : (nb078_alpha_dummy_669) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1664 : (nb078_alpha_dummy_669) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_669, fv_syn_c1c] using (nb078_compact_fv_empty_0496)

theorem nb078_compact_fv_empty_0497 (g : Var) : (nb078_alpha_dummy_672 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1665 (g : Var) : (nb078_alpha_dummy_672 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_672, fv_syn_c1c] using (nb078_compact_fv_empty_0497 g)

theorem nb078_compact_fv_empty_0498 : (nb078_alpha_dummy_667) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1666 : (nb078_alpha_dummy_667) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_667, fv_syn_c1c] using (nb078_compact_fv_empty_0498)

theorem nb078_compact_fv_empty_0499 (g : Var) : (nb078_alpha_dummy_668 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1667 (g : Var) : (nb078_alpha_dummy_668 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_668, fv_syn_c1c] using (nb078_compact_fv_empty_0499 g)

theorem nb078_compact_fv_empty_0500 : (nb078_alpha_dummy_663) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1668 : (nb078_alpha_dummy_663) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_663, fv_syn_c1c] using (nb078_compact_fv_empty_0500)

theorem nb078_compact_fv_empty_0501 (g : Var) : (nb078_alpha_dummy_665 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1669 (g : Var) : (nb078_alpha_dummy_665 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_665, fv_syn_c1c] using (nb078_compact_fv_empty_0501 g)

theorem nb078_compact_fv_empty_0502 : (nb078_alpha_dummy_664) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1670 : (nb078_alpha_dummy_664) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_664, fv_syn_c1c] using (nb078_compact_fv_empty_0502)

theorem nb078_compact_fv_empty_0503 (g : Var) : (nb078_alpha_dummy_666 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1671 (g : Var) : (nb078_alpha_dummy_666 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_666, fv_syn_c1c] using (nb078_compact_fv_empty_0503 g)

theorem nb078_compact_fv_empty_0504 : (nb078_alpha_dummy_656) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1672 : (nb078_alpha_dummy_656) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_656, fv_syn_c1c] using (nb078_compact_fv_empty_0504)

theorem nb078_compact_fv_empty_0505 (g : Var) : (nb078_alpha_dummy_658 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1673 (g : Var) : (nb078_alpha_dummy_658 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_658, fv_syn_c1c] using (nb078_compact_fv_empty_0505 g)

theorem nb078_compact_fv_empty_0506 : (nb078_alpha_dummy_655) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1674 : (nb078_alpha_dummy_655) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_655, fv_syn_c1c] using (nb078_compact_fv_empty_0506)

theorem nb078_compact_fv_empty_0507 (g : Var) : (nb078_alpha_dummy_657 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1675 (g : Var) : (nb078_alpha_dummy_657 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_657, fv_syn_c1c] using (nb078_compact_fv_empty_0507 g)

theorem nb078_compact_fv_empty_0508 : (nb078_alpha_dummy_661) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1676 : (nb078_alpha_dummy_661) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_661, fv_syn_c1c] using (nb078_compact_fv_empty_0508)

theorem nb078_compact_fv_empty_0509 (g : Var) : (nb078_alpha_dummy_662 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1677 (g : Var) : (nb078_alpha_dummy_662 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_662, fv_syn_c1c] using (nb078_compact_fv_empty_0509 g)

theorem nb078_compact_fv_empty_0510 : (nb078_alpha_dummy_659) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1678 : (nb078_alpha_dummy_659) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_659, fv_syn_c1c] using (nb078_compact_fv_empty_0510)

theorem nb078_compact_fv_empty_0511 (g : Var) : (nb078_alpha_dummy_660 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1679 (g : Var) : (nb078_alpha_dummy_660 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_660, fv_syn_c1c] using (nb078_compact_fv_empty_0511 g)

theorem nb078_compact_fv_empty_0512 : (nb078_alpha_dummy_650) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1680 : (nb078_alpha_dummy_650) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_650, fv_syn_c1c] using (nb078_compact_fv_empty_0512)

theorem nb078_compact_fv_empty_0513 (g : Var) : (nb078_alpha_dummy_652 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1681 (g : Var) : (nb078_alpha_dummy_652 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_652, fv_syn_c1c] using (nb078_compact_fv_empty_0513 g)

theorem nb078_compact_fv_empty_0514 : (nb078_alpha_dummy_649) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1682 : (nb078_alpha_dummy_649) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_649, fv_syn_c1c] using (nb078_compact_fv_empty_0514)

theorem nb078_compact_fv_empty_0515 (g : Var) : (nb078_alpha_dummy_651 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1683 (g : Var) : (nb078_alpha_dummy_651 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_651, fv_syn_c1c] using (nb078_compact_fv_empty_0515 g)

theorem nb078_compact_fv_empty_0516 : (nb078_alpha_dummy_653) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1684 : (nb078_alpha_dummy_653) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_653, fv_syn_c1c] using (nb078_compact_fv_empty_0516)

theorem nb078_compact_fv_empty_0517 (g : Var) : (nb078_alpha_dummy_654 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_1685 (g : Var) : (nb078_alpha_dummy_654 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_654, fv_syn_c1c] using (nb078_compact_fv_empty_0517 g)

theorem nb078_compact_envfresh_0224 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670), (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)), ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)), ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)), ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_671) (nb078_alpha_dummy_674 g) (nb078_wpp_notmem_1660) (nb078_wpp_notmem_1661 g) (TEnvFresh.consFresh (nb078_alpha_dummy_670) (nb078_alpha_dummy_673 g) (nb078_wpp_notmem_1662) (nb078_wpp_notmem_1663 g) (TEnvFresh.consFresh (nb078_alpha_dummy_669) (nb078_alpha_dummy_672 g) (nb078_wpp_notmem_1664) (nb078_wpp_notmem_1665 g) (TEnvFresh.consFresh (nb078_alpha_dummy_667) (nb078_alpha_dummy_668 g) (nb078_wpp_notmem_1666) (nb078_wpp_notmem_1667 g) (TEnvFresh.consFresh (nb078_alpha_dummy_663) (nb078_alpha_dummy_665 g) (nb078_wpp_notmem_1668) (nb078_wpp_notmem_1669 g) (TEnvFresh.consFresh (nb078_alpha_dummy_664) (nb078_alpha_dummy_666 g) (nb078_wpp_notmem_1670) (nb078_wpp_notmem_1671 g) (TEnvFresh.consFresh (nb078_alpha_dummy_656) (nb078_alpha_dummy_658 g) (nb078_wpp_notmem_1672) (nb078_wpp_notmem_1673 g) (TEnvFresh.consFresh (nb078_alpha_dummy_655) (nb078_alpha_dummy_657 g) (nb078_wpp_notmem_1674) (nb078_wpp_notmem_1675 g) (TEnvFresh.consFresh (nb078_alpha_dummy_661) (nb078_alpha_dummy_662 g) (nb078_wpp_notmem_1676) (nb078_wpp_notmem_1677 g) (TEnvFresh.consFresh (nb078_alpha_dummy_659) (nb078_alpha_dummy_660 g) (nb078_wpp_notmem_1678) (nb078_wpp_notmem_1679 g) (TEnvFresh.consFresh (nb078_alpha_dummy_650) (nb078_alpha_dummy_652 g) (nb078_wpp_notmem_1680) (nb078_wpp_notmem_1681 g) (TEnvFresh.consFresh (nb078_alpha_dummy_649) (nb078_alpha_dummy_651 g) (nb078_wpp_notmem_1682) (nb078_wpp_notmem_1683 g) (TEnvFresh.consFresh (nb078_alpha_dummy_653) (nb078_alpha_dummy_654 g) (nb078_wpp_notmem_1684) (nb078_wpp_notmem_1685 g) (TEnvFresh.consFresh (nb078_alpha_dummy_571) (nb078_alpha_dummy_574 g) (nb078_wpp_notmem_1590) (nb078_wpp_notmem_1591 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1468) (nb078_wpp_notmem_1469 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1470) (nb078_wpp_notmem_1471 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1472) (nb078_wpp_notmem_1473 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1474) (nb078_wpp_notmem_1475 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1476) (nb078_wpp_notmem_1477 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0224 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670), (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)), ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)), ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)), ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0224 x y g)

theorem nb078_wpp_notmem_1686 : (nb078_alpha_dummy_671) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_671, fv_syn_c0] using (nb078_compact_fv_empty_0492)

theorem nb078_wpp_notmem_1687 (g : Var) : (nb078_alpha_dummy_674 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_674, fv_syn_c0] using (nb078_compact_fv_empty_0493 g)

theorem nb078_wpp_notmem_1688 : (nb078_alpha_dummy_670) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_670, fv_syn_c0] using (nb078_compact_fv_empty_0494)

theorem nb078_wpp_notmem_1689 (g : Var) : (nb078_alpha_dummy_673 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_673, fv_syn_c0] using (nb078_compact_fv_empty_0495 g)

theorem nb078_wpp_notmem_1690 : (nb078_alpha_dummy_669) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_669, fv_syn_c0] using (nb078_compact_fv_empty_0496)

theorem nb078_wpp_notmem_1691 (g : Var) : (nb078_alpha_dummy_672 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_672, fv_syn_c0] using (nb078_compact_fv_empty_0497 g)

theorem nb078_wpp_notmem_1692 : (nb078_alpha_dummy_667) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_667, fv_syn_c0] using (nb078_compact_fv_empty_0498)

theorem nb078_wpp_notmem_1693 (g : Var) : (nb078_alpha_dummy_668 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_668, fv_syn_c0] using (nb078_compact_fv_empty_0499 g)

theorem nb078_wpp_notmem_1694 : (nb078_alpha_dummy_663) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_663, fv_syn_c0] using (nb078_compact_fv_empty_0500)

theorem nb078_wpp_notmem_1695 (g : Var) : (nb078_alpha_dummy_665 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_665, fv_syn_c0] using (nb078_compact_fv_empty_0501 g)

theorem nb078_wpp_notmem_1696 : (nb078_alpha_dummy_664) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_664, fv_syn_c0] using (nb078_compact_fv_empty_0502)

theorem nb078_wpp_notmem_1697 (g : Var) : (nb078_alpha_dummy_666 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_666, fv_syn_c0] using (nb078_compact_fv_empty_0503 g)

theorem nb078_wpp_notmem_1698 : (nb078_alpha_dummy_656) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_656, fv_syn_c0] using (nb078_compact_fv_empty_0504)

theorem nb078_wpp_notmem_1699 (g : Var) : (nb078_alpha_dummy_658 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_658, fv_syn_c0] using (nb078_compact_fv_empty_0505 g)

theorem nb078_wpp_notmem_1700 : (nb078_alpha_dummy_655) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_655, fv_syn_c0] using (nb078_compact_fv_empty_0506)

theorem nb078_wpp_notmem_1701 (g : Var) : (nb078_alpha_dummy_657 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_657, fv_syn_c0] using (nb078_compact_fv_empty_0507 g)

theorem nb078_wpp_notmem_1702 : (nb078_alpha_dummy_661) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_661, fv_syn_c0] using (nb078_compact_fv_empty_0508)

theorem nb078_wpp_notmem_1703 (g : Var) : (nb078_alpha_dummy_662 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_662, fv_syn_c0] using (nb078_compact_fv_empty_0509 g)

theorem nb078_wpp_notmem_1704 : (nb078_alpha_dummy_659) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_659, fv_syn_c0] using (nb078_compact_fv_empty_0510)

theorem nb078_wpp_notmem_1705 (g : Var) : (nb078_alpha_dummy_660 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_660, fv_syn_c0] using (nb078_compact_fv_empty_0511 g)

theorem nb078_wpp_notmem_1706 : (nb078_alpha_dummy_650) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_650, fv_syn_c0] using (nb078_compact_fv_empty_0512)

theorem nb078_wpp_notmem_1707 (g : Var) : (nb078_alpha_dummy_652 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_652, fv_syn_c0] using (nb078_compact_fv_empty_0513 g)

theorem nb078_wpp_notmem_1708 : (nb078_alpha_dummy_649) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_649, fv_syn_c0] using (nb078_compact_fv_empty_0514)

theorem nb078_wpp_notmem_1709 (g : Var) : (nb078_alpha_dummy_651 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_651, fv_syn_c0] using (nb078_compact_fv_empty_0515 g)

theorem nb078_wpp_notmem_1710 : (nb078_alpha_dummy_653) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_653, fv_syn_c0] using (nb078_compact_fv_empty_0516)

theorem nb078_wpp_notmem_1711 (g : Var) : (nb078_alpha_dummy_654 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_654, fv_syn_c0] using (nb078_compact_fv_empty_0517 g)

theorem nb078_compact_envfresh_0225 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670), (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)), ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)), ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)), ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_671) (nb078_alpha_dummy_674 g) (nb078_wpp_notmem_1686) (nb078_wpp_notmem_1687 g) (TEnvFresh.consFresh (nb078_alpha_dummy_670) (nb078_alpha_dummy_673 g) (nb078_wpp_notmem_1688) (nb078_wpp_notmem_1689 g) (TEnvFresh.consFresh (nb078_alpha_dummy_669) (nb078_alpha_dummy_672 g) (nb078_wpp_notmem_1690) (nb078_wpp_notmem_1691 g) (TEnvFresh.consFresh (nb078_alpha_dummy_667) (nb078_alpha_dummy_668 g) (nb078_wpp_notmem_1692) (nb078_wpp_notmem_1693 g) (TEnvFresh.consFresh (nb078_alpha_dummy_663) (nb078_alpha_dummy_665 g) (nb078_wpp_notmem_1694) (nb078_wpp_notmem_1695 g) (TEnvFresh.consFresh (nb078_alpha_dummy_664) (nb078_alpha_dummy_666 g) (nb078_wpp_notmem_1696) (nb078_wpp_notmem_1697 g) (TEnvFresh.consFresh (nb078_alpha_dummy_656) (nb078_alpha_dummy_658 g) (nb078_wpp_notmem_1698) (nb078_wpp_notmem_1699 g) (TEnvFresh.consFresh (nb078_alpha_dummy_655) (nb078_alpha_dummy_657 g) (nb078_wpp_notmem_1700) (nb078_wpp_notmem_1701 g) (TEnvFresh.consFresh (nb078_alpha_dummy_661) (nb078_alpha_dummy_662 g) (nb078_wpp_notmem_1702) (nb078_wpp_notmem_1703 g) (TEnvFresh.consFresh (nb078_alpha_dummy_659) (nb078_alpha_dummy_660 g) (nb078_wpp_notmem_1704) (nb078_wpp_notmem_1705 g) (TEnvFresh.consFresh (nb078_alpha_dummy_650) (nb078_alpha_dummy_652 g) (nb078_wpp_notmem_1706) (nb078_wpp_notmem_1707 g) (TEnvFresh.consFresh (nb078_alpha_dummy_649) (nb078_alpha_dummy_651 g) (nb078_wpp_notmem_1708) (nb078_wpp_notmem_1709 g) (TEnvFresh.consFresh (nb078_alpha_dummy_653) (nb078_alpha_dummy_654 g) (nb078_wpp_notmem_1710) (nb078_wpp_notmem_1711 g) (TEnvFresh.consFresh (nb078_alpha_dummy_571) (nb078_alpha_dummy_574 g) (nb078_wpp_notmem_1612) (nb078_wpp_notmem_1613 g) (TEnvFresh.consFresh (nb078_alpha_dummy_570) (nb078_alpha_dummy_573 g) (nb078_wpp_notmem_1498) (nb078_wpp_notmem_1499 g) (TEnvFresh.consFresh (nb078_alpha_dummy_569) (nb078_alpha_dummy_572 g) (nb078_wpp_notmem_1500) (nb078_wpp_notmem_1501 g) (TEnvFresh.consFresh (nb078_alpha_dummy_575) (nb078_alpha_dummy_576 g) (nb078_wpp_notmem_1502) (nb078_wpp_notmem_1503 g) (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g) (nb078_wpp_notmem_1504) (nb078_wpp_notmem_1505 g) (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g) (nb078_wpp_notmem_1506) (nb078_wpp_notmem_1507 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0788) (nb078_wpp_notmem_0789 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb078_wpp_refl_0225 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_671), (nb078_alpha_dummy_674 g)), ((nb078_alpha_dummy_670), (nb078_alpha_dummy_673 g)), ((nb078_alpha_dummy_669), (nb078_alpha_dummy_672 g)), ((nb078_alpha_dummy_667), (nb078_alpha_dummy_668 g)), ((nb078_alpha_dummy_663), (nb078_alpha_dummy_665 g)), ((nb078_alpha_dummy_664), (nb078_alpha_dummy_666 g)), ((nb078_alpha_dummy_656), (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)), ((nb078_alpha_dummy_661), (nb078_alpha_dummy_662 g)), ((nb078_alpha_dummy_659), (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0225 x y g)

theorem nb078_wpp_notmem_1712 : (nb078_alpha_dummy_667) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_667, fv_syn_cnnc] using (nb078_compact_fv_empty_0498)

theorem nb078_wpp_notmem_1713 (g : Var) : (nb078_alpha_dummy_668 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_668, fv_syn_cnnc] using (nb078_compact_fv_empty_0499 g)

theorem nb078_wpp_notmem_1714 : (nb078_alpha_dummy_663) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_663, fv_syn_cnnc] using (nb078_compact_fv_empty_0500)

theorem nb078_wpp_notmem_1715 (g : Var) : (nb078_alpha_dummy_665 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_665, fv_syn_cnnc] using (nb078_compact_fv_empty_0501 g)

theorem nb078_wpp_notmem_1716 : (nb078_alpha_dummy_664) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_664, fv_syn_cnnc] using (nb078_compact_fv_empty_0502)

theorem nb078_wpp_notmem_1717 (g : Var) : (nb078_alpha_dummy_666 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_666, fv_syn_cnnc] using (nb078_compact_fv_empty_0503 g)

theorem nb078_wpp_notmem_1718 : (nb078_alpha_dummy_656) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_656, fv_syn_cnnc] using (nb078_compact_fv_empty_0504)

theorem nb078_wpp_notmem_1719 (g : Var) : (nb078_alpha_dummy_658 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_658, fv_syn_cnnc] using (nb078_compact_fv_empty_0505 g)

theorem nb078_wpp_notmem_1720 : (nb078_alpha_dummy_655) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_655, fv_syn_cnnc] using (nb078_compact_fv_empty_0506)

theorem nb078_wpp_notmem_1721 (g : Var) : (nb078_alpha_dummy_657 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_657, fv_syn_cnnc] using (nb078_compact_fv_empty_0507 g)

theorem nb078_wpp_notmem_1722 : (nb078_alpha_dummy_661) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_661, fv_syn_cnnc] using (nb078_compact_fv_empty_0508)

theorem nb078_wpp_notmem_1723 (g : Var) : (nb078_alpha_dummy_662 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_662, fv_syn_cnnc] using (nb078_compact_fv_empty_0509 g)

theorem nb078_wpp_notmem_1724 : (nb078_alpha_dummy_659) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_659, fv_syn_cnnc] using (nb078_compact_fv_empty_0510)

theorem nb078_wpp_notmem_1725 (g : Var) : (nb078_alpha_dummy_660 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_660, fv_syn_cnnc] using (nb078_compact_fv_empty_0511 g)

theorem nb078_wpp_notmem_1726 : (nb078_alpha_dummy_650) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_650, fv_syn_cnnc] using (nb078_compact_fv_empty_0512)

theorem nb078_wpp_notmem_1727 (g : Var) : (nb078_alpha_dummy_652 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_652, fv_syn_cnnc] using (nb078_compact_fv_empty_0513 g)

theorem nb078_wpp_notmem_1728 : (nb078_alpha_dummy_649) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_649, fv_syn_cnnc] using (nb078_compact_fv_empty_0514)

theorem nb078_wpp_notmem_1729 (g : Var) : (nb078_alpha_dummy_651 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_651, fv_syn_cnnc] using (nb078_compact_fv_empty_0515 g)

theorem nb078_wpp_notmem_1730 : (nb078_alpha_dummy_653) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_653, fv_syn_cnnc] using (nb078_compact_fv_empty_0516)

theorem nb078_wpp_notmem_1731 (g : Var) : (nb078_alpha_dummy_654 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_654, fv_syn_cnnc] using (nb078_compact_fv_empty_0517 g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
