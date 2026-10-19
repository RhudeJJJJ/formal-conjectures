/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Compact exact univariate certificates. Affine identities are certified by
rational evaluations and a proved degree bound, not by numerical sampling.
-/
import Proofs.RadenkovicGutmanCheckedRoots
import Proofs.RadenkovicGutmanRationalTensorFast

namespace Gebendorfer.RadenkovicGutman.HornerCertificates
open Polynomial Set
abbrev Poly := List ℚ

noncomputable def evaluate (p : Poly) (x : ℝ) : ℝ := (CheckedRoots.polynomial p).eval x

@[simp] theorem evaluate_nil (x : ℝ) : evaluate [] x = 0 := by simp [evaluate, CheckedRoots.polynomial]
@[simp] theorem evaluate_cons (c : ℚ) (p : Poly) (x : ℝ) :
    evaluate (c :: p) x = (c : ℝ) + x * evaluate p x := by
  simp [evaluate, CheckedRoots.polynomial]

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | c :: p, d :: q => (c + d) :: add p q

def scale (c : ℚ) (p : Poly) : Poly := p.map (fun a => c * a)

theorem evaluate_add (p q : Poly) (x : ℝ) : evaluate (add p q) x = evaluate p x + evaluate q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons c p ih =>
    cases q with
    | nil => simp [add]
    | cons d q => simp only [add, evaluate_cons, Rat.cast_add, ih]; ring

theorem evaluate_scale (c : ℚ) (p : Poly) (x : ℝ) :
    evaluate (scale c p) x = (c : ℝ) * evaluate p x := by
  induction p with
  | nil => simp [scale]
  | cons d p ih => simp only [scale, List.map_cons, evaluate_cons, Rat.cast_mul] at *; rw [ih]; ring

def margin (u v j : Poly) (L s : ℚ) : Poly :=
  add j (scale (-L) (add (scale (1 + s) u) (scale (1 + 1 / s) v)))

theorem evaluate_margin (u v j : Poly) (L s : ℚ) (x : ℝ) :
    evaluate (margin u v j L s) x = evaluate j x -
      (L : ℝ) * ((1 + (s : ℝ)) * evaluate u x + (1 + 1 / (s : ℝ)) * evaluate v x) := by
  simp only [margin, evaluate_add, evaluate_scale, Rat.cast_neg, Rat.cast_add,
    Rat.cast_one, Rat.cast_div]
  ring

def tensorFrom : ℕ → Poly → RationalTensorPolynomial.Poly 1
  | _, [] => []
  | n, c :: p => (c, fun _ => n) :: tensorFrom (n + 1) p

theorem tensorFrom_evaluate (p : Poly) (n : ℕ) (x : ℝ) :
    RationalTensorPolynomial.evaluate (fun _ : Fin 1 => x) (tensorFrom n p) =
      x ^ n * evaluate p x := by
  induction p generalizing n with
  | nil => simp [tensorFrom, RationalTensorPolynomial.evaluate]
  | cons c p ih =>
    simp only [tensorFrom, RationalTensorPolynomial.evaluate, RationalTensorPolynomial.monomial,
      Fin.prod_univ_one, evaluate_cons, ih, pow_succ]
    ring

def accepts (M : ℕ) (p : Poly) : Bool :=
  RationalTensorPolynomial.acceptsFast (fun _ : Fin 1 => M) (tensorFrom 0 p)

theorem accepts_sound (M : ℕ) (p : Poly) (h : accepts M p = true)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ evaluate p x := by
  have hp := RationalTensorPolynomial.acceptsFast_sound (fun _ : Fin 1 => M)
    (tensorFrom 0 p) h (fun _ => x) (fun _ => hx)
  simpa only [tensorFrom_evaluate, pow_zero, one_mul] using hp

/-- M+1 exact rational evaluations establish an affine polynomial identity. -/
def affineCheck (M : ℕ) (p a : Poly) (l w : ℚ) : Bool :=
  decide (p.length ≤ M + 1 ∧ a.length ≤ M + 1 ∧
    ∀ k : Fin (M + 1), CheckedRoots.eval a k.val =
      CheckedRoots.eval p (l + w * k.val))

theorem affineCheck_sound (M : ℕ) (p a : Poly) (l w : ℚ)
    (hc : affineCheck M p a l w = true) (x : ℝ) :
    evaluate a x = evaluate p ((l : ℝ) + w * x) := by
  obtain ⟨hp, ha, hs⟩ := of_decide_eq_true hc
  let linear : ℝ[X] := C (l : ℝ) + C (w : ℝ) * X
  have hP : (CheckedRoots.polynomial p).natDegree ≤ M := by
    have := CheckedRoots.degree_bound p
    omega
  have hA : (CheckedRoots.polynomial a).natDegree ≤ M := by
    have := CheckedRoots.degree_bound a
    omega
  have hlin : linear.natDegree ≤ 1 := by dsimp [linear]; compute_degree
  have hcomp : ((CheckedRoots.polynomial p).comp linear).natDegree ≤ M := by
    have h := Polynomial.natDegree_comp_le (p := CheckedRoots.polynomial p) (q := linear)
    exact h.trans (by simpa using Nat.mul_le_mul hP hlin)
  have he : CheckedRoots.polynomial a = (CheckedRoots.polynomial p).comp linear := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _
      (f := fun k : Fin (M + 1) => (k.val : ℝ))
    · intro i j h
      apply Fin.ext
      change (i.val : ℝ) = (j.val : ℝ) at h
      exact_mod_cast h
    · intro k
      have h := congrArg (fun z : ℚ => (z : ℝ)) (hs k)
      rw [CheckedRoots.eval_cast, CheckedRoots.eval_cast] at h
      simpa [linear, Polynomial.eval_comp] using h
    · simp only [Fintype.card_fin]
      omega
  change (CheckedRoots.polynomial a).eval x = _
  rw [he, Polynomial.eval_comp]
  simp only [linear, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, evaluate]

theorem evaluate_append (p q : Poly) (x : ℝ) :
    evaluate (p ++ q) x = evaluate p x + x ^ p.length * evaluate q x := by
  induction p with
  | nil => simp
  | cons c p ih =>
    simp only [List.cons_append, evaluate_cons, List.length_cons, pow_succ, ih]
    ring

theorem reverse_scaled (p : Poly) (x : ℝ) (hx : x ≠ 0) :
    x ^ p.length * evaluate p.reverse (1 / x) = x * evaluate p x := by
  induction p with
  | nil => simp
  | cons c p ih =>
    rw [List.reverse_cons, evaluate_append]
    simp only [List.length_cons, List.length_reverse, evaluate_cons, evaluate_nil,
      mul_zero, add_zero]
    rw [pow_succ]
    have he : x ^ p.length * (1 / x) ^ p.length = (1 : ℝ) := by
      rw [← mul_pow]
      simp [hx]
    calc
      x ^ p.length * x * (evaluate p.reverse (1 / x) + (1 / x) ^ p.length * c) =
          x * (x ^ p.length * evaluate p.reverse (1 / x)) +
            x * (x ^ p.length * (1 / x) ^ p.length) * c := by ring
      _ = x * (x * evaluate p x) + x * c := by rw [ih, he]; ring
      _ = x * ((c : ℝ) + x * evaluate p x) := by ring

def specialize (p : List Poly) (d : ℚ) : Poly := p.map (fun c => CheckedRoots.eval c d)

noncomputable def nestedEvaluate : List Poly → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | c :: p, d, x => evaluate c d + x * nestedEvaluate p d x

theorem specialize_sound (p : List Poly) (d : ℚ) (x : ℝ) :
    evaluate (specialize p d) x = nestedEvaluate p (d : ℝ) x := by
  induction p with
  | nil => simp [specialize, nestedEvaluate]
  | cons c p ih =>
    simp only [specialize, List.map_cons, evaluate_cons, nestedEvaluate] at *
    rw [CheckedRoots.eval_cast]
    change evaluate c (d : ℝ) + x * _ = _
    rw [ih]

theorem cell_sound (M : ℕ) (u v j a : Poly) (L s l w : ℚ)
    (ha : affineCheck M (margin u v j L s) a l w = true)
    (hb : accepts M a = true) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ evaluate j ((l : ℝ) + w * t) - (L : ℝ) *
      ((1 + (s : ℝ)) * evaluate u ((l : ℝ) + w * t) +
        (1 + 1 / (s : ℝ)) * evaluate v ((l : ℝ) + w * t)) := by
  have h := accepts_sound M a hb t ht
  rw [affineCheck_sound M _ _ _ _ ha, evaluate_margin] at h
  exact h

theorem reverse_margin_sound (u v j : Poly) (n : ℕ)
    (hu : u.length = n) (hv : v.length = n) (hj : j.length = n)
    (L s y : ℝ) (hy : 0 < y)
    (h : 0 ≤ evaluate j.reverse (1 / y) - L *
      ((1 + s) * evaluate u.reverse (1 / y) + (1 + 1 / s) * evaluate v.reverse (1 / y))) :
    0 ≤ evaluate j y - L * ((1 + s) * evaluate u y + (1 + 1 / s) * evaluate v y) := by
  have hU := reverse_scaled u y hy.ne'
  have hV := reverse_scaled v y hy.ne'
  have hJ := reverse_scaled j y hy.ne'
  rw [hu] at hU
  rw [hv] at hV
  rw [hj] at hJ
  have hm := mul_nonneg (pow_nonneg hy.le n) h
  have he : y ^ n * (evaluate j.reverse (1 / y) - L *
      ((1 + s) * evaluate u.reverse (1 / y) + (1 + 1 / s) * evaluate v.reverse (1 / y))) =
      y * (evaluate j y - L * ((1 + s) * evaluate u y + (1 + 1 / s) * evaluate v y)) := by
    calc
      _ = y ^ n * evaluate j.reverse (1 / y) - L *
          ((1 + s) * (y ^ n * evaluate u.reverse (1 / y)) +
            (1 + 1 / s) * (y ^ n * evaluate v.reverse (1 / y))) := by ring
      _ = _ := by rw [hU, hV, hJ]; ring
  rw [he] at hm
  by_contra hn
  have hn' := mul_neg_of_pos_of_neg hy (lt_of_not_ge hn)
  linarith

#print axioms specialize_sound
#print axioms cell_sound
#print axioms reverse_margin_sound
#print axioms evaluate_add
#print axioms evaluate_scale
#print axioms evaluate_margin
#print axioms tensorFrom_evaluate
#print axioms accepts_sound
#print axioms affineCheck_sound
#print axioms evaluate_append
#print axioms reverse_scaled
end Gebendorfer.RadenkovicGutman.HornerCertificates
