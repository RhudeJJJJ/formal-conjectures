/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Kernel-checkable rational sign and degree certificates for complete root boxes.
Coefficients are listed in increasing order. Repeated factors are handled
separately; this checker certifies a factor with distinct real roots.
-/
import Proofs.RadenkovicGutmanRootIsolation

namespace Gebendorfer.RadenkovicGutman.CheckedRoots
open Polynomial Set Finset

def eval : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

noncomputable def polynomial : List ℚ → ℝ[X]
  | [] => 0
  | c :: cs => C (c : ℝ) + X * polynomial cs

theorem eval_cast (cs : List ℚ) (x : ℚ) :
    (eval cs x : ℝ) = (polynomial cs).eval (x : ℝ) := by
  induction cs with
  | nil => simp [eval, polynomial]
  | cons c cs ih => simp [eval, polynomial, ih]

theorem degree_bound (cs : List ℚ) : (polynomial cs).natDegree ≤ cs.length - 1 := by
  induction cs with
  | nil => simp [polynomial]
  | cons c cs ih =>
    cases cs with
    | nil => simp [polynomial]
    | cons d ds =>
      have hm := Polynomial.natDegree_mul_le (p := (X : ℝ[X])) (q := polynomial (d :: ds))
      have ha := Polynomial.natDegree_add_le (C (c : ℝ)) (X * polynomial (d :: ds))
      simp only [Polynomial.natDegree_X, Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)] at ha hm
      change (C (c : ℝ) + X * polynomial (d :: ds)).natDegree ≤ (c :: d :: ds).length - 1
      simp only [List.length_cons] at ih ⊢
      omega

def accepts (cs : List ℚ) (n : ℕ) (a b : Fin n → ℚ) : Bool :=
  decide (0 < n ∧ cs.length ≤ n + 1 ∧ ∀ i,
    a i < b i ∧ eval cs (a i) * eval cs (b i) < 0 ∧
      ∀ j, i < j → b i ≤ a j)

private theorem conditions (cs : List ℚ) (n : ℕ) (a b : Fin n → ℚ)
    (hc : accepts cs n a b = true) :
    polynomial cs ≠ 0 ∧ (polynomial cs).natDegree ≤ n ∧
      (∀ i, (a i : ℝ) < b i) ∧
      (∀ i, (polynomial cs).eval (a i : ℝ) * (polynomial cs).eval (b i : ℝ) < 0) ∧
      (∀ i j, i < j → (b i : ℝ) ≤ a j) := by
  obtain ⟨hn, hlen, hrows⟩ := of_decide_eq_true hc
  have hs (i : Fin n) :
      (polynomial cs).eval (a i : ℝ) * (polynomial cs).eval (b i : ℝ) < 0 := by
    rw [← eval_cast, ← eval_cast]
    exact_mod_cast (hrows i).2.1
  refine ⟨?_, ?_, ?_, hs, ?_⟩
  · intro hp
    have h := hs ⟨0, hn⟩
    simp [hp] at h
  · have hd := degree_bound cs
    omega
  · intro i
    exact_mod_cast (hrows i).1
  · intro i j hij
    exact_mod_cast (hrows i).2.2 j hij

theorem complete (cs : List ℚ) (n : ℕ) (a b : Fin n → ℚ)
    (hc : accepts cs n a b = true) :
    ∃ r : Fin n → ℝ, (∀ i, r i ∈ Ioo (a i : ℝ) (b i : ℝ)) ∧
      (polynomial cs).roots = Multiset.map r (Finset.univ : Finset (Fin n)).val := by
  obtain ⟨hp, hn, hab, hs, ho⟩ := conditions cs n a b hc
  exact RootIsolation.complete_roots _ hp n hn _ _ hab hs ho

theorem stop_loss_bounds (cs : List ℚ) (n : ℕ) (a b : Fin n → ℚ)
    (hc : accepts cs n a b = true) (α : ℝ) :
    (∑ i, max ((a i : ℝ) - α) 0) ≤
      ((polynomial cs).roots.map (fun x => max (x - α) 0)).sum ∧
    ((polynomial cs).roots.map (fun x => max (x - α) 0)).sum ≤
      ∑ i, max ((b i : ℝ) - α) 0 := by
  obtain ⟨hp, hn, hab, hs, ho⟩ := conditions cs n a b hc
  exact RootIsolation.stop_loss_bounds _ hp n hn _ _ hab hs ho α

def cubic : List ℚ := [-7, 19, -9, 1]
def cubicLower : Fin 3 → ℚ := ![46/100, 248/100, 605/100]
def cubicUpper : Fin 3 → ℚ := ![47/100, 249/100, 606/100]

theorem cubic_accepts : accepts cubic 3 cubicLower cubicUpper = true := by decide +kernel

theorem cubic_stop_loss_upper :
    ((polynomial cubic).roots.map (fun x => max (x - (12/7 : ℝ)) 0)).sum ≤ 717/140 := by
  have h := (stop_loss_bounds cubic 3 cubicLower cubicUpper cubic_accepts (12/7)).2
  norm_num [cubicUpper, Fin.sum_univ_succ] at h ⊢
  exact h

#print axioms degree_bound
#print axioms complete
#print axioms stop_loss_bounds
#print axioms cubic_accepts
#print axioms cubic_stop_loss_upper
end Gebendorfer.RadenkovicGutman.CheckedRoots
