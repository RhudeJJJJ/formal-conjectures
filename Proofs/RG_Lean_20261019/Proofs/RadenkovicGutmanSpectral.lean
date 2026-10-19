/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.

Spectral foundations for the Radenković--Gutman formalization.
This file proves the exact energy/stop-loss identity for actual graph
Laplacians. It does not assert the unformalized strict fusion inequality.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

namespace Gebendorfer.RadenkovicGutman

open Finset

variable {ι : Type*} [Fintype ι]

noncomputable def stopLoss (eigenvalue : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, max (eigenvalue i - t) 0

noncomputable def centredEnergy (eigenvalue : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, |eigenvalue i - t|

theorem abs_eq_two_positivePart_sub (x : ℝ) : |x| = 2 * max x 0 - x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_right hx']
    ring

/-- The exact finite spectral identity; no integral representation is assumed. -/
theorem energy_eq_two_stopLoss_sub_trace (eigenvalue : ι → ℝ) (t : ℝ) :
    centredEnergy eigenvalue t = 2 * stopLoss eigenvalue t -
      ((∑ i, eigenvalue i) - (Fintype.card ι : ℝ) * t) := by
  unfold centredEnergy stopLoss
  simp_rw [abs_eq_two_positivePart_sub]
  rw [sum_sub_distrib, ← mul_sum, sum_sub_distrib]
  simp

theorem energy_eq_two_stopLoss (eigenvalue : ι → ℝ) (t : ℝ)
    (htrace : ∑ i, eigenvalue i = (Fintype.card ι : ℝ) * t) :
    centredEnergy eigenvalue t = 2 * stopLoss eigenvalue t := by
  rw [energy_eq_two_stopLoss_sub_trace, htrace]
  ring

theorem stopLoss_lipschitz (eigenvalue : ι → ℝ) (s t : ℝ) :
    |stopLoss eigenvalue s - stopLoss eigenvalue t| ≤
      (Fintype.card ι : ℝ) * |s - t| := by
  unfold stopLoss
  rw [← sum_sub_distrib]
  calc
    |∑ i, (max (eigenvalue i - s) 0 - max (eigenvalue i - t) 0)| ≤
        ∑ i, |max (eigenvalue i - s) 0 - max (eigenvalue i - t) 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, |s - t| := by
      apply sum_le_sum
      intro i _
      have hi := abs_max_sub_max_le_abs (eigenvalue i - s) (eigenvalue i - t) 0
      have heq : eigenvalue i - s - (eigenvalue i - t) = -(s - t) := by ring
      simpa only [heq, abs_neg] using hi
    _ = _ := by simp

/-- The strict spectral counting function, as a real-valued finite sum. -/
noncomputable def aboveCount (eigenvalue : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if t < eigenvalue i then 1 else 0

theorem positivePart_right_derivative (a t : ℝ) :
    HasDerivWithinAt (fun x : ℝ => max (a - x) 0)
      (if t < a then -1 else 0) (Set.Ici t) t := by
  split_ifs with h
  · have hd : HasDerivAt (fun x : ℝ => a - x) (-1) t := by
      simpa using! (hasDerivAt_const t a).sub (hasDerivAt_id t)
    have heq : (fun x : ℝ => max (a - x) 0) =ᶠ[nhds t] (fun x => a - x) := by
      filter_upwards [gt_mem_nhds h] with x hx
      exact max_eq_left (sub_nonneg.mpr hx.le)
    exact (hd.congr_of_eventuallyEq heq).hasDerivWithinAt
  · apply (hasDerivWithinAt_const t (Set.Ici t) (0 : ℝ)).congr
    · intro x hx
      exact max_eq_right (sub_nonpos.mpr ((le_of_not_gt h).trans hx))
    · exact max_eq_right (sub_nonpos.mpr (le_of_not_gt h))

theorem stopLoss_right_derivative (eigenvalue : ι → ℝ) (t : ℝ) :
    HasDerivWithinAt (stopLoss eigenvalue) (-aboveCount eigenvalue t) (Set.Ici t) t := by
  classical
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ)
    (fun i _ => positivePart_right_derivative (eigenvalue i) t)
  have heq : (∑ i, if t < eigenvalue i then (-1 : ℝ) else 0) =
      -aboveCount eigenvalue t := by
    unfold aboveCount
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num
  rw [heq] at h
  exact h

/-- A one-unit count gap gives the dimension-free transport estimate. -/
theorem stopLoss_difference_lipschitz (a b : ι → ℝ)
    (hcount : ∀ x, |aboveCount a x - aboveCount b x| ≤ 1) (s t : ℝ) :
    |(stopLoss a s - stopLoss b s) - (stopLoss a t - stopLoss b t)| ≤ |s - t| := by
  wlog hst : s ≤ t generalizing s t
  · have h := this t s (le_of_not_ge hst)
    simpa only [abs_sub_comm] using h
  have hc : ContinuousOn (fun x => stopLoss a x - stopLoss b x) (Set.Icc s t) := by
    unfold stopLoss
    fun_prop
  have hd : ∀ x ∈ Set.Ico s t,
      HasDerivWithinAt (fun y => stopLoss a y - stopLoss b y)
        (-aboveCount a x - -aboveCount b x) (Set.Ici x) x := by
    intro x _
    exact (stopLoss_right_derivative a x).sub (stopLoss_right_derivative b x)
  have hb : ∀ x ∈ Set.Ico s t, ‖-aboveCount a x - -aboveCount b x‖ ≤ (1 : ℝ) := by
    intro x _
    simpa only [Real.norm_eq_abs, neg_sub_neg, abs_sub_comm] using hcount x
  have hm := norm_image_sub_le_of_norm_deriv_right_le_segment hc hd hb t ⟨hst, le_rfl⟩
  calc
    _ = |(stopLoss a t - stopLoss b t) - (stopLoss a s - stopLoss b s)| :=
      abs_sub_comm _ _
    _ ≤ _ := by
      simpa only [Real.norm_eq_abs, one_mul, abs_sub_comm s t,
        abs_of_nonneg (sub_nonneg.mpr hst)] using hm

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def meanDegree : ℝ :=
  (2 * G.edgeFinset.card : ℝ) / Fintype.card V

noncomputable def laplacianSpectrum : V → ℝ :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues

noncomputable def laplacianEnergy : ℝ :=
  centredEnergy (laplacianSpectrum G) (meanDegree G)

theorem laplacian_trace : (G.lapMatrix ℝ).trace = (2 * G.edgeFinset.card : ℝ) := by
  have hs := G.sum_degrees_eq_twice_card_edges
  have hsR := congrArg (fun n : ℕ => (n : ℝ)) hs
  push_cast at hsR
  simpa [Matrix.trace, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix] using hsR

theorem spectrum_sum : ∑ v, laplacianSpectrum G v = (2 * G.edgeFinset.card : ℝ) := by
  simpa [laplacianSpectrum] using
    ((G.isHermitian_lapMatrix ℝ).trace_eq_sum_eigenvalues).symm.trans (laplacian_trace G)

theorem spectrum_mean [Nonempty V] :
    ∑ v, laplacianSpectrum G v = (Fintype.card V : ℝ) * meanDegree G := by
  rw [spectrum_sum]
  unfold meanDegree
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Equation (2.1) of the RG manuscript, now attached to the actual Laplacian. -/
theorem laplacianEnergy_eq_stopLoss [Nonempty V] :
    laplacianEnergy G = 2 * stopLoss (laplacianSpectrum G) (meanDegree G) := by
  exact energy_eq_two_stopLoss _ _ (spectrum_mean G)

theorem laplacianEnergy_nonneg : 0 ≤ laplacianEnergy G := by
  exact sum_nonneg (fun _ _ => abs_nonneg _)

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Equal edge counts give the exact comparison at a common mean degree. -/
theorem energy_difference_eq_twice_stopLoss_difference [Nonempty V]
    (hedges : G.edgeFinset.card = H.edgeFinset.card) :
    laplacianEnergy G - laplacianEnergy H =
      2 * (stopLoss (laplacianSpectrum G) (meanDegree G) -
           stopLoss (laplacianSpectrum H) (meanDegree G)) := by
  rw [laplacianEnergy_eq_stopLoss, laplacianEnergy_eq_stopLoss]
  have hm : meanDegree H = meanDegree G := by simp [meanDegree, hedges]
  rw [hm]
  ring

theorem strict_comparison_iff [Nonempty V]
    (hedges : G.edgeFinset.card = H.edgeFinset.card) :
    laplacianEnergy H < laplacianEnergy G ↔
      stopLoss (laplacianSpectrum H) (meanDegree G) <
      stopLoss (laplacianSpectrum G) (meanDegree G) := by
  have h := energy_difference_eq_twice_stopLoss_difference G H hedges
  constructor <;> intro hlt <;> linarith

omit [DecidableEq V] in
/-- The common mean degree of any nonempty finite tree. -/
theorem tree_meanDegree (hG : G.IsTree) :
    meanDegree G = 2 - 2 / (Fintype.card V : ℝ) := by
  have hn := hG.connected.nonempty
  have hp : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have he : (G.edgeFinset.card : ℝ) + 1 = Fintype.card V := by
    exact_mod_cast hG.card_edgeFinset
  unfold meanDegree
  field_simp
  nlinarith

/-- In particular the manuscript's centering is exactly the tree centering. -/
theorem tree_energy_identity (hG : G.IsTree) :
    laplacianEnergy G =
      2 * stopLoss (laplacianSpectrum G) (2 - 2 / (Fintype.card V : ℝ)) := by
  have hn := hG.connected.nonempty
  rw [laplacianEnergy_eq_stopLoss, tree_meanDegree G hG]

/-- The path-minimum target itself, with no proof supplied or assumed. -/
noncomputable def PathMinimum : Prop := by
  classical
  exact ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
    T.IsTree → laplacianEnergy (SimpleGraph.pathGraph n) ≤ laplacianEnergy T

#print axioms energy_eq_two_stopLoss_sub_trace
#print axioms energy_eq_two_stopLoss
#print axioms positivePart_right_derivative
#print axioms stopLoss_right_derivative
#print axioms stopLoss_difference_lipschitz
#print axioms stopLoss_lipschitz
#print axioms laplacian_trace
#print axioms spectrum_sum
#print axioms laplacianEnergy_eq_stopLoss
#print axioms strict_comparison_iff
#print axioms tree_meanDegree
#print axioms tree_energy_identity

end Gebendorfer.RadenkovicGutman

