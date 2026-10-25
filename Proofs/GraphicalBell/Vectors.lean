import Mathlib.Tactic.Ring
import Mathlib.Tactic.Omega

namespace GraphicalBellProof
abbrev Vector := ℤ → ℤ

def step (d : ℤ) (a : Vector) : Vector := fun k => a (k - 1) + (k - d) * a k

def tower (a : Vector) : ℕ → Vector
  | 0 => a
  | t + 1 => step 0 (tower a t)

def basis (q : ℕ) : Vector := fun k => if k = (q : ℤ) then 1 else 0

def candidate (q r t : ℕ) : Vector := step (r : ℤ) (tower (basis q) t)

def Nonnegative (a : Vector) : Prop := ∀ k, 0 ≤ a k

def Supported (a : Vector) : Prop := ∀ k, k < 0 → a k = 0

lemma step_comm (d e : ℤ) (a : Vector) : step d (step e a) = step e (step d a) := by
  funext k
  simp only [step]
  ring

lemma step_add (d : ℤ) (a b : Vector) : step d (a + b) = step d a + step d b := by
  funext k
  simp only [step, Pi.add_apply]
  ring

lemma step_sub (d : ℤ) (a b : Vector) : step d (a - b) = step d a - step d b := by
  funext k
  simp only [step, Pi.sub_apply]
  ring

lemma step_tower (d : ℤ) (a : Vector) (t : ℕ) :
    step d (tower a t) = tower (step d a) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [tower]
      rw [step_comm, ih]

lemma tower_tower (a : Vector) (s t : ℕ) : tower (tower a s) t = tower a (s + t) := by
  induction t with
  | zero => simp [tower]
  | succ t ih => simpa only [tower, Nat.add_succ] using congrArg (step 0) ih

lemma step_basis (q : ℕ) : step (q : ℤ) (basis q) = basis (q + 1) := by
  funext k
  by_cases h : k = (q : ℤ) + 1
  · subst k
    simp [step, basis]
  · have hprev : k - 1 ≠ (q : ℤ) := by omega
    simp only [step, basis, if_neg hprev]
    by_cases heq : k = (q : ℤ)
    · subst k
      simp
    · simp [heq, h]

lemma basis_nonnegative (q : ℕ) : Nonnegative (basis q) := by
  intro k
  simp only [basis]
  split <;> omega

lemma basis_supported (q : ℕ) : Supported (basis q) := by
  intro k hk
  simp only [basis, if_neg (show k ≠ (q : ℤ) by omega)]

lemma step_supported (d : ℤ) {a : Vector} (ha : Supported a) : Supported (step d a) := by
  intro k hk
  simp [step, ha k hk, ha (k - 1) (by omega)]

lemma step_zero_nonnegative {a : Vector} (ha : Nonnegative a) (hs : Supported a) :
    Nonnegative (step 0 a) := by
  intro k
  by_cases hk : 0 ≤ k
  · exact add_nonneg (ha _) (mul_nonneg (by simpa using hk) (ha _))
  · have hh : k < 0 := by omega
    rw [step_supported 0 hs k hh]

lemma tower_nonnegative {a : Vector} (ha : Nonnegative a) (hs : Supported a) (t : ℕ) :
    Nonnegative (tower a t) ∧ Supported (tower a t) := by
  induction t with
  | zero => exact ⟨ha, hs⟩
  | succ t ih => exact ⟨step_zero_nonnegative ih.1 ih.2, step_supported 0 ih.2⟩

lemma basis_tower_nonnegative (q t : ℕ) : Nonnegative (tower (basis q) t) :=
  (tower_nonnegative (basis_nonnegative q) (basis_supported q) t).1

lemma lower_support (q t : ℕ) : ∀ k : ℤ, k < q → tower (basis q) t k = 0 := by
  induction t with
  | zero =>
      intro k hk
      simp [tower, basis, show k ≠ (q : ℤ) by omega]
  | succ t ih =>
      intro k hk
      simp [tower, step, ih k hk, ih (k - 1) (by omega)]

lemma candidate_nonnegative (q r t : ℕ) (hr : r ≤ q) : Nonnegative (candidate q r t) := by
  intro k
  by_cases hk : k < q
  · simp [candidate, step, lower_support q t k hk,
      lower_support q t (k - 1) (by omega)]
  · exact add_nonneg (basis_tower_nonnegative q t _) (mul_nonneg (by omega)
      (basis_tower_nonnegative q t _))

lemma two_steps_difference (d r : ℤ) (a : Vector) :
    step d (step (r - d) a) - step 0 (step r a) = fun k => d * (r - d) * a k := by
  funext k
  simp only [step, Pi.sub_apply]
  ring

lemma shifted_steps_difference (q d r : ℤ) (a : Vector) :
    step d (step (q - d + r) a) - step q (step r a) =
      fun k => (q - d) * (d - r) * a k := by
  funext k
  simp only [step, Pi.sub_apply]
  ring

lemma compare_same_clique (q r d t : ℕ) (hd : d ≤ r) (k : ℤ) :
    candidate q r (t + 1) k ≤ step (d : ℤ) (candidate q (r - d) t) k := by
  have h := congrFun (two_steps_difference (d : ℤ) (r : ℤ) (tower (basis q) t)) k
  have hc : (0 : ℤ) ≤ (d : ℤ) * ((r : ℤ) - d) * tower (basis q) t k :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (basis_tower_nonnegative q t k)
  have hh : candidate q r (t + 1) = step 0 (step (r : ℤ) (tower (basis q) t)) := by
    simp only [candidate, tower, step_comm (r : ℤ) 0]
  rw [hh]
  unfold candidate
  rw [Nat.cast_sub hd]
  change step (d : ℤ) (step ((r : ℤ) - d) (tower (basis q) t)) k -
    step 0 (step (r : ℤ) (tower (basis q) t)) k = _ at h
  omega

lemma compare_previous_clique (q r d t : ℕ) (hd : d ≤ q) (hr : r < d) (k : ℤ) :
    candidate (q + 1) r t k ≤ step (d : ℤ) (candidate q (q - d + r) t) k := by
  have h := congrFun (shifted_steps_difference (q : ℤ) (d : ℤ) (r : ℤ)
    (tower (basis q) t)) k
  have hc : (0 : ℤ) ≤ ((q : ℤ) - d) * ((d : ℤ) - r) * tower (basis q) t k :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (basis_tower_nonnegative q t k)
  have hh : candidate (q + 1) r t = step (q : ℤ) (step (r : ℤ)
      (tower (basis q) t)) := by
    rw [candidate, ← step_basis, ← step_tower, step_comm]
  rw [hh]
  unfold candidate
  rw [Nat.cast_add, Nat.cast_sub hd]
  change step (d : ℤ) (step ((q : ℤ) - d + r) (tower (basis q) t)) k -
    step (q : ℤ) (step (r : ℤ) (tower (basis q) t)) k = _ at h
  omega

end GraphicalBellProof
