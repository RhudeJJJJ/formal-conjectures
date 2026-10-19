/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Exact nested Horner certificates for complete parameter boxes.
No numerical sampling is used as a proof: the interpolation checker checks
degree bounds and a complete rational grid, and Bernstein positivity is proved.
-/
import Proofs.RadenkovicGutmanTensorPolynomial

namespace Gebendorfer.RadenkovicGutman.NestedHorner
open Polynomial Set Finset
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

abbrev Poly : ℕ → Type
  | 0 => ℚ
  | n + 1 => List (Poly n)

def zero : (n : ℕ) → Poly n
  | 0 => 0
  | _ + 1 => []

def zipAdd {A : Type*} (f : A → A → A) : List A → List A → List A
  | [], q => q
  | p, [] => p
  | c :: p, d :: q => f c d :: zipAdd f p q

def add : {n : ℕ} → Poly n → Poly n → Poly n
  | 0, p, q => p + q
  | _ + 1, p, q => zipAdd add p q

def scale (c : ℚ) : {n : ℕ} → Poly n → Poly n
  | 0, p => c * p
  | _ + 1, p => p.map (scale c)

noncomputable def eval : {n : ℕ} → Poly n → (Fin n → ℝ) → ℝ
  | 0, p, _ => p
  | _ + 1, p, x => p.foldr (fun c z => eval c (fun i => x i.succ) + x 0 * z) 0

@[simp] theorem eval_nil {n : ℕ} (x : Fin (n+1) → ℝ) : eval ([] : Poly (n+1)) x = 0 := rfl
@[simp] theorem eval_cons {n : ℕ} (c : Poly n) (p : Poly (n+1)) (x : Fin (n+1) → ℝ) :
    eval (c :: p) x = eval c (fun i => x i.succ) + x 0 * eval p x := rfl

@[simp] theorem eval_zero (n : ℕ) (x : Fin n → ℝ) : eval (zero n) x = 0 := by
  cases n <;> simp [zero, eval]

theorem eval_add {n : ℕ} (p q : Poly n) (x : Fin n → ℝ) :
    eval (add p q) x = eval p x + eval q x := by
  induction n with
  | zero => simp [add, eval]
  | succ n ih =>
    induction p generalizing q with
    | nil => simp [add, zipAdd]
    | cons c p hp =>
      cases q with
      | nil => simp [add, zipAdd]
      | cons d q =>
        change eval (add c d) (fun i => x i.succ) + x 0 * eval (add p q) x = _
        rw [ih, hp]
        simp only [eval_cons]
        ring

theorem eval_scale (c : ℚ) {n : ℕ} (p : Poly n) (x : Fin n → ℝ) :
    eval (scale c p) x = (c : ℝ) * eval p x := by
  induction n with
  | zero => simp [scale, eval]
  | succ n ih =>
    induction p with
    | nil => simp [scale]
    | cons d p hp =>
      simp only [scale, List.map_cons, eval_cons] at *
      rw [ih, hp]
      ring

def pointValue {n : ℕ} : Poly (n+1) → ℚ → Poly n
  | [], _ => zero n
  | c :: p, t => add c (scale t (pointValue p t))

theorem pointValue_sound {n : ℕ} (p : Poly (n+1)) (t : ℚ) (x : Fin n → ℝ) :
    eval (pointValue p t) x = eval p (Fin.cons (t : ℝ) x) := by
  induction p with
  | nil => simp [pointValue]
  | cons c p ih => simp only [pointValue, eval_add, eval_scale, eval_cons, Fin.cons_succ,
      Fin.cons_zero, ih]

noncomputable def parameterPolynomial {n : ℕ} : Poly (n+1) → (Fin n → ℝ) → ℝ[X]
  | [], _ => 0
  | c :: p, x => C (eval c x) + X * parameterPolynomial p x

theorem parameterPolynomial_eval {n : ℕ} (p : Poly (n+1)) (x : Fin n → ℝ) (t : ℝ) :
    (parameterPolynomial p x).eval t = eval p (Fin.cons t x) := by
  induction p with
  | nil => simp [parameterPolynomial]
  | cons c p ih => simp only [parameterPolynomial, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, ih, eval_cons, Fin.cons_succ, Fin.cons_zero]

theorem parameterPolynomial_degree {n : ℕ} (p : Poly (n+1)) (x : Fin n → ℝ) :
    (parameterPolynomial p x).natDegree ≤ p.length - 1 := by
  induction p with
  | nil => simp [parameterPolynomial]
  | cons c p ih =>
    cases p with
    | nil => simp [parameterPolynomial]
    | cons d ds =>
      have hm := Polynomial.natDegree_mul_le (p := (X : ℝ[X])) (q := parameterPolynomial (d :: ds) x)
      have ha := Polynomial.natDegree_add_le (C (eval c x)) (X * parameterPolynomial (d :: ds) x)
      simp only [Polynomial.natDegree_X, Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)] at ha hm
      change (C (eval c x) + X * parameterPolynomial (d :: ds) x).natDegree ≤ _
      simp only [List.length_cons] at ih ⊢
      omega

def affineCheck : (n : ℕ) → (Fin n → ℕ) → Poly n → Poly n → (Fin n → ℚ) → (Fin n → ℚ) → Bool
  | 0, _, p, a, _, _ => decide (a = p)
  | n+1, d, p, a, l, w => decide (p.length ≤ d 0 + 1 ∧ a.length ≤ d 0 + 1 ∧
      ∀ k : Fin (d 0 + 1), affineCheck n (fun i => d i.succ)
        (pointValue p (l 0 + w 0 * k.val)) (pointValue a k.val)
        (fun i => l i.succ) (fun i => w i.succ) = true)

noncomputable section
theorem affineCheck_sound (n : ℕ) (d : Fin n → ℕ) (p a : Poly n) (l w : Fin n → ℚ)
    (hc : affineCheck n d p a l w = true) (x : Fin n → ℝ) :
    eval a x = eval p (fun i => (l i : ℝ) + (w i : ℝ) * x i) := by
  induction n with
  | zero =>
    have h : a = p := of_decide_eq_true hc
    subst a
    rfl
  | succ n ih =>
    obtain ⟨hp, ha, hs⟩ := of_decide_eq_true hc
    let inner : Fin n → ℝ := fun i => (l i.succ : ℝ) + (w i.succ : ℝ) * x i.succ
    let linear : ℝ[X] := C (l 0 : ℝ) + C (w 0 : ℝ) * X
    have hP : (parameterPolynomial p inner).natDegree ≤ d 0 := by
      have := parameterPolynomial_degree p inner
      omega
    have hA : (parameterPolynomial a (fun i => x i.succ)).natDegree ≤ d 0 := by
      have := parameterPolynomial_degree a (fun i => x i.succ)
      omega
    have hlin : linear.natDegree ≤ 1 := by dsimp [linear]; compute_degree
    have hcomp : ((parameterPolynomial p inner).comp linear).natDegree ≤ d 0 := by
      have h := Polynomial.natDegree_comp_le (p := parameterPolynomial p inner) (q := linear)
      exact h.trans (by simpa using Nat.mul_le_mul hP hlin)
    have he : parameterPolynomial a (fun i => x i.succ) = (parameterPolynomial p inner).comp linear := by
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _
        (f := fun k : Fin (d 0 + 1) => (k.val : ℝ))
      · intro i j h
        apply Fin.ext
        change (i.val : ℝ) = (j.val : ℝ) at h
        exact_mod_cast h
      · intro k
        have h := ih _ _ _ _ _ (hs k) (fun i => x i.succ)
        rw [pointValue_sound, pointValue_sound] at h
        simp only [Polynomial.eval_comp, linear, Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_mul, Polynomial.eval_X, parameterPolynomial_eval]
        simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] using h
      · simp only [Fintype.card_fin]
        omega
    have h := congrArg (fun z : ℝ[X] => z.eval (x 0)) he
    simp only [Polynomial.eval_comp, linear, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, parameterPolynomial_eval] at h
    convert h using 1
    · congr 1
      exact (Fin.cons_self_tail x).symm
    · congr 1
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end
def coefficientFrom {n : ℕ} (D j : ℕ) : ℕ → Poly (n+1) → Poly n
  | _, [] => zero n
  | k, c :: p => add (if k ≤ j then scale (Nat.fast_choose (D-k) (j-k)) c else zero n)
      (coefficientFrom D j (k+1) p)

def positiveCheck : (n : ℕ) → (Fin n → ℕ) → Poly n → Bool
  | 0, _, p => decide (0 ≤ p)
  | n+1, d, p => decide (p.length ≤ d 0 + 1 ∧
      ∀ j : Fin (d 0 + 1), positiveCheck n (fun i => d i.succ) (coefficientFrom (d 0) j.val 0 p) = true)

noncomputable section
theorem coefficientFrom_cons {n : ℕ} (D j k : ℕ) (c : Poly n) (p : Poly (n+1)) (x : Fin n → ℝ) :
    eval (coefficientFrom D j k (c :: p)) x =
      (if k ≤ j then (Nat.choose (D-k) (j-k) : ℝ) else 0) * eval c x +
        eval (coefficientFrom D j (k+1) p) x := by
  by_cases h : k ≤ j <;> simp [coefficientFrom, h, eval_add, eval_scale, ← Nat.choose_eq_fast_choose]

theorem representation {n : ℕ} (D : ℕ) (p : Poly (n+1)) (x : Fin n → ℝ) (t : ℝ)
    (k : ℕ) (hp : k + p.length ≤ D+1) :
    t ^ k * eval p (Fin.cons t x) = ∑ j : Fin (D+1),
      eval (coefficientFrom D j.val k p) x * (t ^ j.val * (1-t) ^ (D-j.val)) := by
  induction p generalizing k with
  | nil => simp [coefficientFrom]
  | cons c p ih =>
    have hk : k ≤ D := by simp only [List.length_cons] at hp; omega
    have hr := ih (k+1) (by simp only [List.length_cons] at hp; omega)
    have ht : t ^ k = ∑ j : Fin (D+1),
        (if k ≤ j.val then (Nat.choose (D-k) (j.val-k) : ℝ) else 0) *
          (t ^ j.val * (1-t) ^ (D-j.val)) := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (if k ≤ j then (Nat.choose (D-k) (j-k) : ℝ) else 0) * (t ^ j * (1-t) ^ (D-j))) (D+1)]
      simpa only [ite_mul, zero_mul, mul_assoc] using TensorPolynomial.power_expansion D k hk t
    calc
      _ = eval c x * t ^ k + t ^ (k+1) * eval p (Fin.cons t x) := by
        simp only [eval_cons, Fin.cons_succ, Fin.cons_zero, pow_succ]
        ring
      _ = _ := by
        rw [ht, hr, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [coefficientFrom_cons]
        ring

theorem positiveCheck_sound (n : ℕ) (d : Fin n → ℕ) (p : Poly n)
    (hc : positiveCheck n d p = true) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    0 ≤ eval p x := by
  induction n with
  | zero =>
    change (0 : ℝ) ≤ (p : ℝ)
    exact_mod_cast (of_decide_eq_true hc : (0 : ℚ) ≤ p)
  | succ n ih =>
    obtain ⟨hp, hs⟩ := of_decide_eq_true hc
    have he := representation (d 0) p (fun i => x i.succ) (x 0) 0 (by omega)
    have hvec : Fin.cons (x 0) (fun i => x i.succ) = x := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    simp only [pow_zero, one_mul, hvec] at he
    rw [he]
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (ih _ _ (hs j) _ (fun i => hx i.succ))
    exact mul_nonneg (pow_nonneg (hx 0).1 _) (pow_nonneg (sub_nonneg.mpr (hx 0).2) _)

#print axioms eval_add
#print axioms pointValue_sound
#print axioms affineCheck_sound
#print axioms representation
#print axioms positiveCheck_sound
end
end Gebendorfer.RadenkovicGutman.NestedHorner
