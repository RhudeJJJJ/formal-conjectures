/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedIntegerHybrid

/-! Power coefficients in nonnegative coordinates, followed by a bounded box.
The original integer coefficients and complete bounded domains are retained. -/
namespace Gebendorfer.RadenkovicGutman.NestedIntegerMixed
open Set NestedInteger
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def accepts (n : ℕ) (d : Fin n → ℕ) : (k : ℕ) → Poly (n+k) → Bool
  | 0, p => NestedIntegerHybrid.accepts n d p
  | k+1, p => p.all (accepts n d k)

def Domain (n : ℕ) : (k : ℕ) → (Fin (n+k) → ℝ) → Prop
  | 0, x => ∀ i, x i ∈ Icc (0 : ℝ) 1
  | k+1, x => 0 ≤ x 0 ∧ Domain n k (fun i => x i.succ)

theorem accepts_sound (n : ℕ) (d : Fin n → ℕ) (k : ℕ) (p : Poly (n+k))
    (hc : accepts n d k p = true) (x : Fin (n+k) → ℝ) (hx : Domain n k x) :
    0 ≤ NestedHorner.eval (castPoly (n+k) p) x := by
  induction k with
  | zero => exact NestedIntegerHybrid.accepts_sound n d p hc x hx
  | succ k ih =>
    induction p with
    | nil => exact le_rfl
    | cons c p hp =>
      have hh : accepts n d k c = true ∧ p.all (accepts n d k) = true := by
        simpa only [accepts,List.all_cons,Bool.and_eq_true] using hc
      change 0 ≤ NestedHorner.eval (castPoly (n+k) c) (fun i => x i.succ)+
        x 0*NestedHorner.eval (castPoly (n+(k+1)) p) x
      exact add_nonneg (ih c hh.1 _ hx.2) (mul_nonneg hx.1 (hp hh.2))

#print axioms accepts_sound
end Gebendorfer.RadenkovicGutman.NestedIntegerMixed
