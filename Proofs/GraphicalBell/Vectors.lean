import Lean.Elab.Tactic.Omega

namespace GraphicalBellProof
abbrev Vector := Int → Int

def step (d : Int) (a : Vector) : Vector := fun k => a (k - 1) + (k - d) * a k

def tower (a : Vector) : Nat → Vector
  | 0 => a
  | t + 1 => step 0 (tower a t)

def basis (q : Nat) : Vector := fun k => if k = (q : Int) then 1 else 0

def candidate (q r t : Nat) : Vector := step (r : Int) (tower (basis q) t)

def Nonnegative (a : Vector) : Prop := ∀ k, 0 ≤ a k

def Supported (a : Vector) : Prop := ∀ k, k < 0 → a k = 0

theorem step_comm (d e : Int) (a : Vector) : step d (step e a) = step e (step d a) := by
  funext k
  simp only [step]
  simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm, Int.one_mul]
  omega

theorem step_add (d : Int) (a b : Vector) : step d (fun k => a k + b k) = fun k => step d a k + step d b k := by
  funext k
  simp only [step]
  simp only [Int.mul_add, Int.mul_sub, Int.mul_comm]
  omega

theorem step_sub (d : Int) (a b : Vector) : step d (fun k => a k - b k) = fun k => step d a k - step d b k := by
  funext k
  simp only [step]
  simp only [Int.mul_sub, Int.mul_comm]
  omega

theorem step_tower (d : Int) (a : Vector) (t : Nat) :
    step d (tower a t) = tower (step d a) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [tower]
      rw [step_comm, ih]

theorem tower_tower (a : Vector) (s t : Nat) : tower (tower a s) t = tower a (s + t) := by
  induction t with
  | zero => simp [tower]
  | succ t ih =>
      have h : s + (t + 1) = (s + t) + 1 := by omega
      rw [h, tower, ih]
      rfl

theorem step_basis (q : Nat) : step (q : Int) (basis q) = basis (q + 1) := by
  funext k
  by_cases h : k = (q : Int) + 1
  · subst k
    have hqq : (q : Int) + 1 ≠ (q : Int) := by omega
    simp [step, basis, Int.natCast_add, hqq]
  · have hprev : k - 1 ≠ (q : Int) := by omega
    simp only [step, basis, if_neg hprev]
    by_cases heq : k = (q : Int)
    · subst k
      simp [Int.natCast_add, h]
    · simp [heq, Int.natCast_add, h]

theorem basis_nonnegative (q : Nat) : Nonnegative (basis q) := by
  intro k
  simp only [basis]
  split <;> omega

theorem basis_supported (q : Nat) : Supported (basis q) := by
  intro k hk
  simp only [basis, if_neg (show k ≠ (q : Int) by omega)]

theorem step_supported (d : Int) {a : Vector} (ha : Supported a) : Supported (step d a) := by
  intro k hk
  simp [step, ha k hk, ha (k - 1) (by omega)]

theorem step_zero_nonnegative {a : Vector} (ha : Nonnegative a) (hs : Supported a) :
    Nonnegative (step 0 a) := by
  intro k
  by_cases hk : 0 ≤ k
  · exact Int.add_nonneg (ha _) (Int.mul_nonneg (by simpa using hk) (ha _))
  · have hh : k < 0 := by omega
    rw [step_supported 0 hs k hh]
    omega

theorem tower_nonnegative {a : Vector} (ha : Nonnegative a) (hs : Supported a) (t : Nat) :
    Nonnegative (tower a t) ∧ Supported (tower a t) := by
  induction t with
  | zero => exact ⟨ha, hs⟩
  | succ t ih => exact ⟨step_zero_nonnegative ih.1 ih.2, step_supported 0 ih.2⟩

theorem basis_tower_nonnegative (q t : Nat) : Nonnegative (tower (basis q) t) :=
  (tower_nonnegative (basis_nonnegative q) (basis_supported q) t).1

theorem lower_support (q t : Nat) : ∀ k : Int, k < q → tower (basis q) t k = 0 := by
  induction t with
  | zero =>
      intro k hk
      simp [tower, basis, show k ≠ (q : Int) by omega]
  | succ t ih =>
      intro k hk
      simp [tower, step, ih k hk, ih (k - 1) (by omega)]

theorem candidate_nonnegative (q r t : Nat) (hr : r ≤ q) : Nonnegative (candidate q r t) := by
  intro k
  by_cases hk : k < q
  · simp [candidate, step, lower_support q t k hk,
      lower_support q t (k - 1) (by omega)]
  · exact Int.add_nonneg (basis_tower_nonnegative q t _) (Int.mul_nonneg (by omega)
      (basis_tower_nonnegative q t _))

theorem two_steps_difference (d r : Int) (a : Vector) :
    (fun k => step d (step (r - d) a) k - step 0 (step r a) k) = fun k => d * (r - d) * a k := by
  funext k
  simp only [step]
  simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.mul_assoc,
    Int.mul_comm, Int.mul_left_comm, Int.one_mul]
  omega

theorem shifted_steps_difference (q d r : Int) (a : Vector) :
    (fun k => step d (step (q - d + r) a) k - step q (step r a) k) =
      fun k => (q - d) * (d - r) * a k := by
  funext k
  simp only [step]
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_comm, Int.mul_left_comm, Int.one_mul]
  omega

theorem compare_same_clique (q r d t : Nat) (hd : d ≤ r) (k : Int) :
    candidate q r (t + 1) k ≤ step (d : Int) (candidate q (r - d) t) k := by
  have h := congrFun (two_steps_difference (d : Int) (r : Int) (tower (basis q) t)) k
  have hc : (0 : Int) ≤ (d : Int) * ((r : Int) - d) * tower (basis q) t k :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (basis_tower_nonnegative q t k)
  have hh : candidate q r (t + 1) = step 0 (step (r : Int) (tower (basis q) t)) := by
    simp only [candidate, tower, step_comm (r : Int) 0]
  rw [hh]
  unfold candidate
  rw [Int.ofNat_sub hd]
  change step (d : Int) (step ((r : Int) - d) (tower (basis q) t)) k -
    step 0 (step (r : Int) (tower (basis q) t)) k = _ at h
  omega

theorem compare_previous_clique (q r d t : Nat) (hd : d ≤ q) (hr : r < d) (k : Int) :
    candidate (q + 1) r t k ≤ step (d : Int) (candidate q (q - d + r) t) k := by
  have h := congrFun (shifted_steps_difference (q : Int) (d : Int) (r : Int)
    (tower (basis q) t)) k
  have hc : (0 : Int) ≤ ((q : Int) - d) * ((d : Int) - r) * tower (basis q) t k :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (basis_tower_nonnegative q t k)
  have hh : candidate (q + 1) r t = step (q : Int) (step (r : Int)
      (tower (basis q) t)) := by
    rw [candidate, ← step_basis, ← step_tower, step_comm]
  rw [hh]
  unfold candidate
  rw [Int.natCast_add, Int.ofNat_sub hd]
  change step (d : Int) (step ((q : Int) - d + r) (tower (basis q) t)) k -
    step (q : Int) (step (r : Int) (tower (basis q) t)) k = _ at h
  omega

end GraphicalBellProof
