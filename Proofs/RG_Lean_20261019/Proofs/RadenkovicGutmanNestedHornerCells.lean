/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Uniform exact box margins and reciprocal ordinate coordinates.
-/
import Proofs.RadenkovicGutmanNestedHorner
import Proofs.RadenkovicGutmanHornerCertificates

namespace Gebendorfer.RadenkovicGutman.NestedHorner
open Set
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def margin {n : ℕ} (u v j : Poly n) (L s : ℚ) : Poly n :=
  add j (scale (-L) (add (scale (1+s) u) (scale (1+1/s) v)))

theorem eval_margin {n : ℕ} (u v j : Poly n) (L s : ℚ) (x : Fin n → ℝ) :
    eval (margin u v j L s) x = eval j x - (L : ℝ) *
      ((1+(s : ℝ)) * eval u x + (1+1/(s : ℝ)) * eval v x) := by
  simp only [margin, eval_add, eval_scale, Rat.cast_neg, Rat.cast_add, Rat.cast_one, Rat.cast_div]
  ring

theorem box_margin_sound (n : ℕ) (d : Fin n → ℕ) (u v j a : Poly n)
    (L s : ℚ) (l w : Fin n → ℚ)
    (ha : affineCheck n d (margin u v j L s) a l w = true)
    (hb : positiveCheck n d a = true) (x : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hx : ∀ i, x i ∈ Icc (l i : ℝ) ((l i : ℝ)+w i)) :
    0 ≤ eval j x - (L : ℝ) * ((1+(s : ℝ)) * eval u x + (1+1/(s : ℝ)) * eval v x) := by
  let t : Fin n → ℝ := fun i => (x i - (l i : ℝ)) / (w i : ℝ)
  have ht : ∀ i, t i ∈ Icc (0 : ℝ) 1 := by
    intro i
    have hi : (0 : ℝ) < w i := by exact_mod_cast hw i
    constructor
    · exact div_nonneg (sub_nonneg.mpr (hx i).1) hi.le
    · apply (div_le_one hi).mpr
      linarith [(hx i).2]
  have h := positiveCheck_sound n d a hb t ht
  rw [affineCheck_sound n d _ _ _ _ ha, eval_margin] at h
  have he : (fun i => (l i : ℝ)+(w i : ℝ)*t i) = x := by
    ext i
    have hi : (w i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hw i)
    dsimp [t]
    field_simp
    ring
  simpa only [he] using h

def reverseLast : (n : ℕ) → ℕ → Poly n → Poly n
  | 0, _, p => p
  | 1, M, p => (p ++ List.replicate (M+1-p.length) 0).reverse
  | n+2, M, p => p.map (reverseLast (n+1) M)

theorem box_scaled_margin_sound (n : ℕ) (d : Fin n → ℕ) (u v j a : Poly n)
    (K L s : ℚ) (hK : 0 < K) (l w : Fin n → ℚ)
    (ha : affineCheck n d (scale K (margin u v j L s)) a l w = true)
    (hb : positiveCheck n d a = true) (x : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hx : ∀ i, x i ∈ Icc (l i : ℝ) ((l i : ℝ)+w i)) :
    0 ≤ eval j x-(L : ℝ)*((1+(s : ℝ))*eval u x+(1+1/(s : ℝ))*eval v x) := by
  let t : Fin n → ℝ := fun i => (x i-(l i : ℝ))/(w i : ℝ)
  have ht : ∀ i, t i ∈ Icc (0 : ℝ) 1 := by
    intro i
    have hi : (0 : ℝ) < w i := by exact_mod_cast hw i
    constructor
    · exact div_nonneg (sub_nonneg.mpr (hx i).1) hi.le
    · apply (div_le_one hi).mpr
      linarith [(hx i).2]
  have h := positiveCheck_sound n d a hb t ht
  rw [affineCheck_sound n d _ _ _ _ ha, eval_scale, eval_margin] at h
  have he : (fun i => (l i : ℝ)+(w i : ℝ)*t i) = x := by
    ext i
    have hi : (w i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hw i)
    dsimp [t]
    field_simp
    ring
  rw [he] at h
  exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hK)

def lastBound : (n : ℕ) → ℕ → Poly n → Bool
  | 0, _, _ => true
  | 1, M, p => decide (p.length ≤ M+1)
  | n+2, M, p => p.all (lastBound (n+1) M)

noncomputable def lastValue : {n : ℕ} → (Fin n → ℝ) → ℝ
  | 0, _ => 1
  | 1, x => x 0
  | _+2, x => lastValue (fun i => x i.succ)

noncomputable def inverseLast : {n : ℕ} → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, x => x
  | 1, x => fun _ => 1 / x 0
  | _+2, x => Fin.cons (x 0) (inverseLast (fun i => x i.succ))

theorem univariate_eval (p : Poly 1) (x : Fin 1 → ℝ) :
    eval p x = HornerCertificates.evaluate p (x 0) := by
  induction p with
  | nil => change (0 : ℝ) = HornerCertificates.evaluate [] (x 0); simp
  | cons c p ih =>
    change (c : ℝ)+x 0*eval p x = _
    rw [ih, HornerCertificates.evaluate_cons]

private theorem evaluate_zeros (m : ℕ) (y : ℝ) :
    HornerCertificates.evaluate (List.replicate m 0) y = 0 := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih]

theorem reverseLast_sound (n M : ℕ) (p : Poly n) (hb : lastBound n M p = true)
    (x : Fin n → ℝ) (hy : 0 < lastValue x) :
    lastValue x ^ M * eval (reverseLast n M p) (inverseLast x) = eval p x := by
  induction n with
  | zero => simp [lastValue, reverseLast, inverseLast]
  | succ n ih =>
    cases n with
    | zero =>
      have hp : p.length ≤ M+1 := of_decide_eq_true hb
      let pad := p ++ List.replicate (M+1-p.length) 0
      have hlen : pad.length = M+1 := by dsimp [pad]; simp only [List.length_append, List.length_replicate]; omega
      have hev (y : ℝ) : HornerCertificates.evaluate pad y = HornerCertificates.evaluate p y := by
        simp [pad, HornerCertificates.evaluate_append, evaluate_zeros]
      have h := HornerCertificates.reverse_scaled pad (x 0) (show x 0 ≠ 0 from hy.ne')
      rw [hlen, hev] at h
      simp only [lastValue, reverseLast, univariate_eval, inverseLast]
      change x 0 ^ M * HornerCertificates.evaluate pad.reverse (1/x 0) = _
      rw [pow_succ] at h
      have hy0 : 0 < x 0 := hy
      nlinarith
    | succ n =>
      induction p with
      | nil => change lastValue x ^ M * 0 = 0; ring
      | cons c p hp =>
        have hparts : lastBound (n+1) M c = true ∧ p.all (lastBound (n+1) M) = true := by
          simpa only [lastBound, List.all_cons, Bool.and_eq_true] using hb
        have hc := ih c hparts.1 (fun i => x i.succ) hy
        have hr := hp hparts.2
        change lastValue (fun i => x i.succ) ^ M *
            (eval (reverseLast (n+1) M c) (inverseLast (fun i => x i.succ)) +
              x 0 * eval (reverseLast (n+2) M p) (inverseLast x)) =
            eval c (fun i => x i.succ) + x 0 * eval p x
        calc
          _ = lastValue (fun i => x i.succ) ^ M * eval (reverseLast (n+1) M c) (inverseLast (fun i => x i.succ)) +
              x 0 * (lastValue x ^ M * eval (reverseLast (n+2) M p) (inverseLast x)) := by
            change _ = lastValue (fun i => x i.succ) ^ M * _ + x 0 * (lastValue (fun i => x i.succ) ^ M * _)
            ring
          _ = _ := by rw [hc, hr]


theorem reverse_margin_sound (n M : ℕ) (u v j : Poly n)
    (hu : lastBound n M u = true) (hv : lastBound n M v = true) (hj : lastBound n M j = true)
    (L s : ℝ) (x : Fin n → ℝ) (hy : 0 < lastValue x)
    (h : 0 ≤ eval (reverseLast n M j) (inverseLast x) - L *
      ((1+s)*eval (reverseLast n M u) (inverseLast x) +
        (1+1/s)*eval (reverseLast n M v) (inverseLast x))) :
    0 ≤ eval j x-L*((1+s)*eval u x+(1+1/s)*eval v x) := by
  have hU := reverseLast_sound n M u hu x hy
  have hV := reverseLast_sound n M v hv x hy
  have hJ := reverseLast_sound n M j hj x hy
  have hp := mul_nonneg (pow_nonneg hy.le M) h
  have he : lastValue x ^ M * (eval (reverseLast n M j) (inverseLast x)-L*
      ((1+s)*eval (reverseLast n M u) (inverseLast x)+(1+1/s)*eval (reverseLast n M v) (inverseLast x))) =
      eval j x-L*((1+s)*eval u x+(1+1/s)*eval v x) := by
    calc
      _ = lastValue x ^ M * eval (reverseLast n M j) (inverseLast x)-L*
          ((1+s)*(lastValue x ^ M * eval (reverseLast n M u) (inverseLast x))+
            (1+1/s)*(lastValue x ^ M * eval (reverseLast n M v) (inverseLast x))) := by ring
      _ = _ := by rw [hU, hV, hJ]
  rwa [he] at hp

#print axioms box_margin_sound
#print axioms reverseLast_sound
#print axioms reverse_margin_sound
end Gebendorfer.RadenkovicGutman.NestedHorner
