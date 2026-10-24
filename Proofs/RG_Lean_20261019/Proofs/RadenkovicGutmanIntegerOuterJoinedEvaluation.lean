/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerOuterPieces

/-!
# Compose evaluated integer transform pieces

This is the existing append identity with checked intermediate data, an explicit
next index and an evaluated suffix. The proof keeps every reconstruction premise.
-/
namespace Gebendorfer.RadenkovicGutman.IntegerOuterJoinedEvaluation
open NestedInteger NestedHorner
noncomputable section

theorem joined {n : ℕ} (l w D : ℤ) (k next : ℕ)
    (p q original a b combined : NestedInteger.Poly (n+1))
    (hi : k+p.length=next) (ho : p++q=original)
    (ha : a=IntegerOuterTerms.transform l w D k p)
    (hb : ∀ x : Fin (n+1) → ℝ,
      eval (castPoly (n+1) b) x=
        eval (castPoly (n+1) (IntegerOuterTerms.transform l w D next q)) x)
    (hc : combined=NestedInteger.add (NestedInteger.scale (D^q.length) a) b)
    (x : Fin (n+1) → ℝ) :
    eval (castPoly (n+1) combined) x=
      eval (castPoly (n+1) (IntegerOuterTerms.transform l w D k original)) x := by
  calc
    _ = (D : ℝ)^q.length*
        eval (castPoly (n+1) (IntegerOuterTerms.transform l w D k p)) x+
        eval (castPoly (n+1) (IntegerOuterTerms.transform l w D (k+p.length) q)) x := by
      rw [hc,cast_add,eval_add,cast_scale,eval_scale,ha,hb,hi]
      push_cast <;> rfl
    _ = eval (castPoly (n+1) (IntegerOuterTerms.transform l w D k (p++q))) x :=
      (IntegerOuterPieces.eval_append l w D k p q x).symm
    _ = _ := by rw [ho]

#print axioms joined
end
end Gebendorfer.RadenkovicGutman.IntegerOuterJoinedEvaluation
