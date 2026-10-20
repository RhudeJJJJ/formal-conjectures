/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedIntegerHybrid

/-! Assemble exact child-polynomial checks without evaluating the entire
closed Boolean certificate again during theorem elaboration. -/
namespace Gebendorfer.RadenkovicGutman.NestedIntegerHybrid
open NestedInteger

theorem bernstein_step {n : ℕ} (d : Fin (n+1) → ℕ) (p : Poly (n+1))
    (hp : p.length ≤ d 0+1)
    (hs : ∀ j : Fin (d 0+1), accepts n (fun i => d i.succ)
      (coefficientFrom (d 0) j.val 0 p) = true) : accepts (n+1) d p = true := by
  apply Bool.or_eq_true.mpr
  right
  exact decide_eq_true ⟨hp,hs⟩

#print axioms bernstein_step
end Gebendorfer.RadenkovicGutman.NestedIntegerHybrid
