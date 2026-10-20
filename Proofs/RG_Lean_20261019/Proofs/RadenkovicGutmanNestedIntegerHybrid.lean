/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedInteger

/-! Integer Bernstein checking with an exact power-coefficient shortcut
at every dimension. The shortcut changes computation, not the box or signs. -/
namespace Gebendorfer.RadenkovicGutman.NestedIntegerHybrid
open NestedInteger Set
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def accepts : (n : ℕ) → (Fin n → ℕ) → Poly n → Bool
  | 0, _, p => decide (0 ≤ p)
  | n+1, d, p => powerCheck (n+1) p || decide (p.length ≤ d 0+1 ∧
      ∀ j : Fin (d 0+1), accepts n (fun i => d i.succ) (coefficientFrom (d 0) j.val 0 p) = true)

theorem accepts_sound (n : ℕ) (d : Fin n → ℕ) (p : Poly n) (hc : accepts n d p = true)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    0 ≤ NestedHorner.eval (castPoly n p) x := by
  induction n with
  | zero =>
    change (0 : ℝ) ≤ ((p : ℚ) : ℝ)
    exact_mod_cast (of_decide_eq_true hc : (0 : ℤ) ≤ p)
  | succ n ih =>
    have hh : powerCheck (n+1) p = true ∨
        decide (p.length ≤ d 0+1 ∧ ∀ j : Fin (d 0+1),
          accepts n (fun i => d i.succ) (coefficientFrom (d 0) j.val 0 p) = true) = true := by
      simpa only [accepts,Bool.or_eq_true] using hc
    rcases hh with hp | hb
    · exact powerCheck_sound (n+1) p hp x (fun i => (hx i).1)
    · obtain ⟨hp,hs⟩ := of_decide_eq_true hb
      have he := NestedHorner.representation (d 0) (castPoly (n+1) p)
        (fun i => x i.succ) (x 0) 0 (by simpa only [castPoly,List.length_map,zero_add] using hp)
      have hvec : Fin.cons (x 0) (fun i => x i.succ) = x := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      simp only [pow_zero,one_mul,hvec] at he
      rw [he]
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg
      · rw [← cast_coefficientFrom]
        exact ih _ _ (hs j) _ (fun i => hx i.succ)
      · exact mul_nonneg (pow_nonneg (hx 0).1 _) (pow_nonneg (sub_nonneg.mpr (hx 0).2) _)

#print axioms accepts_sound
end Gebendorfer.RadenkovicGutman.NestedIntegerHybrid
