import WPPCompactSourceSyntax
import NominalWffPrf

namespace NFChoice.DirectNominalPrf.Nominal.NFLiteralHandlers

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax

abbrev Theory : Fol.SentTheory LNF := LiteralHailperinNF

/-- One exact member of the eleven-sentence Hailperin basis. -/
def literalProof (name : HailperinAxiomName) :
    Theory.fst ⊢ (literalAxiomFormula name).fst :=
  Fol.prf.axm (Set.mem_image_of_mem _ (literalAxiom_mem name))

/-- Instantiate the outermost universal of a literal basis sentence. -/
def openAll (f : Fol.formula LNF) (t : Fol.term LNF) : Fol.formula LNF :=
  match f with
  | .all body => body [t // 0]f
  | other => other

def openAll2 (f : Fol.formula LNF) (s t : Fol.term LNF) : Fol.formula LNF :=
  openAll (openAll f s) t

noncomputable def literalAxExtAt (s t : Fol.term LNF) :
    Theory.fst ⊢ openAll2 (literalAxiomFormula .axExt).fst s t := by
  exact Fol.prf.allE₂ _ t (Fol.prf.allE₂ _ s (literalProof .axExt))

noncomputable def literalAxNinAt (s t : Fol.term LNF) :
    Theory.fst ⊢ openAll2 (literalAxiomFormula .axNin).fst s t := by
  exact Fol.prf.allE₂ _ t (Fol.prf.allE₂ _ s (literalProof .axNin))

noncomputable def literalAxSnAt (s : Fol.term LNF) :
    Theory.fst ⊢ openAll (literalAxiomFormula .axSn).fst s := by
  exact Fol.prf.allE₂ _ s (literalProof .axSn)

noncomputable def literalAxXpAt (s : Fol.term LNF) :
    Theory.fst ⊢ openAll (literalAxiomFormula .axXp).fst s := by
  exact Fol.prf.allE₂ _ s (literalProof .axXp)

noncomputable def literalAxCnvAt (s : Fol.term LNF) :
    Theory.fst ⊢ openAll (literalAxiomFormula .axCnv).fst s := by
  exact Fol.prf.allE₂ _ s (literalProof .axCnv)

noncomputable def literalAxSiAt (s : Fol.term LNF) :
    Theory.fst ⊢ openAll (literalAxiomFormula .axSi).fst s := by
  exact Fol.prf.allE₂ _ s (literalProof .axSi)

noncomputable def literalAxIns2At (s : Fol.term LNF) :
    Theory.fst ⊢ openAll (literalAxiomFormula .axIns2).fst s := by
  exact Fol.prf.allE₂ _ s (literalProof .axIns2)

noncomputable def literalAxIns3At (s : Fol.term LNF) :
    Theory.fst ⊢ openAll (literalAxiomFormula .axIns3).fst s := by
  exact Fol.prf.allE₂ _ s (literalProof .axIns3)

noncomputable def literalAxTypeLowerAt (s : Fol.term LNF) :
    Theory.fst ⊢ openAll (literalAxiomFormula .axTypeLower).fst s := by
  exact Fol.prf.allE₂ _ s (literalProof .axTypeLower)

def axExtGoal (x y z : Var) : Wff :=
  .imp (.all z (syn_wb (.objMem z x) (.objMem z y))) (.objEq x y)

def axNinGoal (x y z w : Var) : Wff :=
  syn_wex z (.all w
    (syn_wb (.objMem w z) (syn_wnan (.objMem w x) (.objMem w y))))

def axSnGoal (x y z : Var) : Wff :=
  syn_wex y (.all z (syn_wb (.objMem z y) (.objEq z x)))

def ax1cGoal (x y z w : Var) : Wff :=
  syn_wex x (.all y
    (syn_wb (.objMem y x)
      (syn_wex z (.all w (syn_wb (.objMem w y) (.objEq w z))))))

def axXpGoal (x y z w t : Var) : Wff :=
  syn_wex y (.all z
    (syn_wb (.objMem z y)
      (syn_wex w (syn_wex t
        (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
          (.objMem t x))))))

def axCnvGoal (x y z w : Var) : Wff :=
  syn_wex y (.all z (.all w
    (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y))
      (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)))))

def axSsetGoal (x y z w : Var) : Wff :=
  syn_wex x (.all y (.all z
    (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x))
      (.all w (.imp (.objMem w y) (.objMem w z))))))

def axSiGoal (x y z w : Var) : Wff :=
  syn_wex y (.all z (.all w
    (syn_wb
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y))
      (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))

def axIns2Goal (x y z w t : Var) : Wff :=
  syn_wex y (.all z (.all w (.all t
    (syn_wb
      (.classMem
        (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (.cv y))
      (.classMem (syn_copk (.cv z) (.cv t)) (.cv x))))))

def axIns3Goal (x y z w t : Var) : Wff :=
  syn_wex y (.all z (.all w (.all t
    (syn_wb
      (.classMem
        (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (.cv y))
      (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))))

def axTypeLowerGoal (x y z w : Var) : Wff :=
  syn_wex y (.all z
    (syn_wb (.objMem z y)
      (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x)))))

noncomputable def axExtOfLowering (x y z : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hyz : y ≠ z)
    (hLower : ∀ rho,
      lowerWff rho (axExtGoal x y z) =
        openAll2 (literalAxiomFormula .axExt).fst (&(rho x)) (&(rho y))) :
    NPrf (axExtGoal x y z) :=
  fun rho => by rw [hLower rho]; exact literalAxExtAt (&(rho x)) (&(rho y))

noncomputable def axNinOfLowering (x y z w : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w)
    (hLower : ∀ rho,
      lowerWff rho (axNinGoal x y z w) =
        openAll2 (literalAxiomFormula .axNin).fst (&(rho x)) (&(rho y))) :
    NPrf (axNinGoal x y z w) :=
  fun rho => by rw [hLower rho]; exact literalAxNinAt (&(rho x)) (&(rho y))

noncomputable def axSnOfLowering (x y z : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hyz : y ≠ z)
    (hLower : ∀ rho,
      lowerWff rho (axSnGoal x y z) =
        openAll (literalAxiomFormula .axSn).fst (&(rho x))) :
    NPrf (axSnGoal x y z) :=
  fun rho => by rw [hLower rho]; exact literalAxSnAt (&(rho x))

noncomputable def ax1cOfLowering (x y z w : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w)
    (hLower : ∀ rho,
      lowerWff rho (ax1cGoal x y z w) =
        (literalAxiomFormula .ax1c).fst) :
    NPrf (ax1cGoal x y z w) :=
  fun rho => by rw [hLower rho]; exact literalProof .ax1c

noncomputable def axXpOfLowering (x y z w t : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w) (_hxt : x ≠ t)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hyt : y ≠ t)
    (_hzw : z ≠ w) (_hzt : z ≠ t) (_hwt : w ≠ t)
    (hLower : ∀ rho,
      lowerWff rho (axXpGoal x y z w t) =
        openAll (literalAxiomFormula .axXp).fst (&(rho x))) :
    NPrf (axXpGoal x y z w t) :=
  fun rho => by rw [hLower rho]; exact literalAxXpAt (&(rho x))

noncomputable def axCnvOfLowering (x y z w : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w)
    (hLower : ∀ rho,
      lowerWff rho (axCnvGoal x y z w) =
        openAll (literalAxiomFormula .axCnv).fst (&(rho x))) :
    NPrf (axCnvGoal x y z w) :=
  fun rho => by rw [hLower rho]; exact literalAxCnvAt (&(rho x))

noncomputable def axSsetOfLowering (x y z w : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w)
    (hLower : ∀ rho,
      lowerWff rho (axSsetGoal x y z w) =
        (literalAxiomFormula .axSset).fst) :
    NPrf (axSsetGoal x y z w) :=
  fun rho => by rw [hLower rho]; exact literalProof .axSset

noncomputable def axSiOfLowering (x y z w : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w)
    (hLower : ∀ rho,
      lowerWff rho (axSiGoal x y z w) =
        openAll (literalAxiomFormula .axSi).fst (&(rho x))) :
    NPrf (axSiGoal x y z w) :=
  fun rho => by rw [hLower rho]; exact literalAxSiAt (&(rho x))

noncomputable def axIns2OfLowering (x y z w t : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w) (_hxt : x ≠ t)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hyt : y ≠ t)
    (_hzw : z ≠ w) (_hzt : z ≠ t) (_hwt : w ≠ t)
    (hLower : ∀ rho,
      lowerWff rho (axIns2Goal x y z w t) =
        openAll (literalAxiomFormula .axIns2).fst (&(rho x))) :
    NPrf (axIns2Goal x y z w t) :=
  fun rho => by rw [hLower rho]; exact literalAxIns2At (&(rho x))

noncomputable def axIns3OfLowering (x y z w t : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w) (_hxt : x ≠ t)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hyt : y ≠ t)
    (_hzw : z ≠ w) (_hzt : z ≠ t) (_hwt : w ≠ t)
    (hLower : ∀ rho,
      lowerWff rho (axIns3Goal x y z w t) =
        openAll (literalAxiomFormula .axIns3).fst (&(rho x))) :
    NPrf (axIns3Goal x y z w t) :=
  fun rho => by rw [hLower rho]; exact literalAxIns3At (&(rho x))

noncomputable def axTypeLowerOfLowering (x y z w : Var)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (_hyz : y ≠ z) (_hyw : y ≠ w) (_hzw : z ≠ w)
    (hLower : ∀ rho,
      lowerWff rho (axTypeLowerGoal x y z w) =
        openAll (literalAxiomFormula .axTypeLower).fst (&(rho x))) :
    NPrf (axTypeLowerGoal x y z w) :=
  fun rho => by rw [hLower rho]; exact literalAxTypeLowerAt (&(rho x))

#print axioms axExtOfLowering
#print axioms axNinOfLowering
#print axioms axSnOfLowering
#print axioms ax1cOfLowering
#print axioms axXpOfLowering
#print axioms axCnvOfLowering
#print axioms axSsetOfLowering
#print axioms axSiOfLowering
#print axioms axIns2OfLowering
#print axioms axIns3OfLowering
#print axioms axTypeLowerOfLowering

end NFChoice.DirectNominalPrf.Nominal.NFLiteralHandlers
