/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerOuterTerms

namespace Gebendorfer.RadenkovicGutman.IntegerOuterPieces
open NestedInteger NestedHorner
set_option maxHeartbeats 0
noncomputable section

/-- A partition of the coefficient list retains the original exact transform.
The independently checked pieces can be combined without reducing it again. -/
theorem eval_append {n : ℕ} (l w D : ℤ) (k : ℕ)
    (p q : NestedInteger.Poly (n+1)) (x : Fin (n+1) → ℝ) :
    eval (castPoly (n+1) (IntegerOuterTerms.transform l w D k (p++q))) x=
      (D : ℝ)^q.length*eval (castPoly (n+1) (IntegerOuterTerms.transform l w D k p)) x+
        eval (castPoly (n+1) (IntegerOuterTerms.transform l w D (k+p.length) q)) x := by
  induction p generalizing k with
  | nil => simp [IntegerOuterTerms.transform,castPoly,eval]
  | cons c p ih =>
    simp only [List.cons_append,IntegerOuterTerms.transform,cast_add,eval_add,
      IntegerOuterTerms.eval_term,List.length_append,List.length_cons]
    rw [ih]
    push_cast
    rw [pow_add]
    have hk : k+(p.length+1)=k+1+p.length := by omega
    rw [hk]
    ring

theorem eval_checked_append {n : ℕ} (l w D : ℤ) (k : ℕ)
    (p q a b combined : NestedInteger.Poly (n+1))
    (ha : a=IntegerOuterTerms.transform l w D k p)
    (hb : b=IntegerOuterTerms.transform l w D (k+p.length) q)
    (hc : combined=NestedInteger.add (NestedInteger.scale (D^q.length) a) b)
    (x : Fin (n+1) → ℝ) :
    eval (castPoly (n+1) combined) x=
      eval (castPoly (n+1) (IntegerOuterTerms.transform l w D k (p++q))) x := by
  rw [hc,cast_add,eval_add,cast_scale,eval_scale,ha,hb,eval_append]
  push_cast
  rfl

#print axioms eval_append
#print axioms eval_checked_append
end
end Gebendorfer.RadenkovicGutman.IntegerOuterPieces
