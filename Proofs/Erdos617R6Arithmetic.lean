/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.

Exact arithmetic from the six-colour manuscript. The graph-theoretic inputs
are explicit hypotheses here; this file does not prove the r=6 conjecture.
-/
import Mathlib.Tactic

namespace Gebendorfer.Erdos617R6

/-- The minimum edge count for independence number at most `r`. -/
def qfun (n r : ℕ) : ℕ :=
  (n % r) * (n / r + 1).choose 2 + (r - n % r) * (n / r).choose 2

def basicCritical (q : ℕ) : ℕ := (10 * q - 7 + 2) / 3
def nonOreCritical (q : ℕ) : ℕ := (10 * q - 4 + 2) / 3
def outsideCost (q : ℕ) : ℕ := (5 * (37 - q) + 1) / 2
def packingCap (q : ℕ) : ℕ :=
  if q ≤ 12 then q.choose 2 - 5 * qfun q 6
  else q.choose 2 - 5 * (qfun q 6 + q / 6 - 1)

/-- All numerical core inequalities used in Sections 6--7 of the paper. -/
structure CoreBounds (m q e : ℕ) : Prop where
  orderLower : 7 ≤ q
  orderUpper : q ≤ 37
  smallestColour : m ≤ 111
  criticalLower : basicCritical q ≤ e
  nonOreLower : q % 6 ≠ 1 → nonOreCritical q ≤ e
  exteriorBudget : e + outsideCost q ≤ m
  otherColours : e ≤ packingCap q

/-- Exhaustive symbolic discharge of the finite critical-order range. -/
theorem critical_core_survivors {m q e : ℕ} (h : CoreBounds m q e) :
    m = 111 ∧ ((q = 23 ∧ e = 76) ∨ (q = 25 ∧ e = 81)) := by
  rcases h with ⟨hlo, hhi, hm, hb, hn, ho, hp⟩
  interval_cases q <;>
    norm_num [basicCritical, nonOreCritical, outsideCost, packingCap, qfun,
      Nat.choose] at * <;> omega

theorem no_core_below_111 {m q e : ℕ} (h : CoreBounds m q e) (hm : m ≤ 110) :
    False := by
  have := (critical_core_survivors h).1
  omega

/-- Equality in the exterior degree budget forces an empty cut. -/
theorem endpoint_separation {s r inner cut : ℕ}
    (hbudget : 111 = 76 + s + r) (hout : 35 ≤ r)
    (hincidence : 70 ≤ 2 * inner + cut) (hedges : r = inner + cut) :
    s = 0 ∧ r = 35 ∧ cut = 0 ∧ inner = 35 := by omega

theorem endpoint_separation_25 {s r inner cut : ℕ}
    (hbudget : 111 = 81 + s + r) (hout : 30 ≤ r)
    (hincidence : 60 ≤ 2 * inner + cut) (hedges : r = inner + cut) :
    s = 0 ∧ r = 30 ∧ cut = 0 ∧ inner = 30 := by omega

/-- The thirteen-vertex remainder cannot pay the six colour lower bounds. -/
theorem remainder_thirteen_impossible (edges : Fin 6 → ℕ)
    (hsum : ∑ c, edges c = (13 : ℕ).choose 2) (hzero : 41 ≤ edges 0)
    (hother : ∀ c : Fin 6, c ≠ 0 → 9 ≤ edges c) : False := by
  have h1 := hother 1 (by decide)
  have h2 := hother 2 (by decide)
  have h3 := hother 3 (by decide)
  have h4 := hother 4 (by decide)
  have h5 := hother 5 (by decide)
  simp only [Fin.sum_univ_succ] at hsum
  change edges 0 + (edges 1 + (edges 2 + (edges 3 + (edges 4 + (edges 5 + 0))))) =
    78 at hsum
  omega

/-- At the all-111 endpoint, minimality equalizes every colour class. -/
theorem all_colours_111 (edges : Fin 6 → ℕ)
    (hsum : ∑ c, edges c = 666) (hmin : ∀ c, 111 ≤ edges c) :
    ∀ c, edges c = 111 := by
  intro c
  have hown := hmin c
  have lower : ∑ d ∈ Finset.univ.erase c, 111 ≤
      ∑ d ∈ Finset.univ.erase c, edges d := by
    exact Finset.sum_le_sum (fun d _ => hmin d)
  have hsplit := Finset.sum_erase_add Finset.univ edges (Finset.mem_univ c)
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ c),
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at lower
  norm_num at lower
  omega

#print axioms critical_core_survivors
#print axioms no_core_below_111
#print axioms endpoint_separation
#print axioms endpoint_separation_25
#print axioms remainder_thirteen_impossible
#print axioms all_colours_111

end Gebendorfer.Erdos617R6
