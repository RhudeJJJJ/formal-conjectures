/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.

All-length determinant bridge for the path recurrence.
This file does not assert the strict fusion inequality or global path minimum.
-/
import Proofs.RadenkovicGutmanPathRecurrence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace Gebendorfer.RadenkovicGutman.PathRecurrence

open Matrix Finset

variable {R : Type*} [CommRing R]

instance pathGraphAdjDecidable (n : ℕ) :
    DecidableRel (SimpleGraph.pathGraph n).Adj := by
  intro i j
  exact decidable_of_iff (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    SimpleGraph.pathGraph_adj.symm

/-- Symmetric tridiagonal matrix with unit off-diagonals. -/
def tridiagonal {n : ℕ} (d : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then d i else
    if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

@[simp] theorem tridiagonal_diag {n : ℕ} (d : Fin n → R) (i : Fin n) :
    tridiagonal d i i = d i := by simp [tridiagonal]

theorem tridiagonal_tail {n : ℕ} (d : Fin (n + 1) → R) :
    (tridiagonal d).submatrix Fin.succ Fin.succ =
      tridiagonal (fun i => d i.succ) := by
  ext i j
  simp [tridiagonal, submatrix_apply, Fin.succ_inj, Fin.val_succ]

/-- Continuant recurrence, proved from two exact cofactor expansions. -/
theorem det_tridiagonal {n : ℕ} (d : Fin (n + 2) → R) :
    det (tridiagonal d) =
      d 0 * det (tridiagonal (fun i => d i.succ)) -
        det (tridiagonal (fun i => d i.succ.succ)) := by
  let M := tridiagonal d
  have hminor : (M.submatrix Fin.succ (1 : Fin (n + 2)).succAbove).submatrix
      Fin.succ Fin.succ = tridiagonal (fun i => d i.succ.succ) := by
    ext i j
    simp [M, submatrix_apply, tridiagonal, Fin.succ_inj, Fin.val_succ]
  have hcol : det (M.submatrix Fin.succ (1 : Fin (n + 2)).succAbove) =
      det (tridiagonal (fun i => d i.succ.succ)) := by
    rw [det_succ_column_zero, Fin.sum_univ_succ]
    have hzero : ∀ i : Fin n,
        (M.submatrix Fin.succ (1 : Fin (n + 2)).succAbove) i.succ 0 = 0 := by
      intro i
      simp [M, submatrix_apply, Fin.succAbove_ne_zero_zero, tridiagonal,
        Fin.val_succ, Fin.ext_iff]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hminor]
    simp [M, submatrix_apply, Fin.succAbove_ne_zero_zero, tridiagonal,
      Fin.val_succ]
  rw [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hzero : ∀ i : Fin n, M 0 i.succ.succ = 0 := by
    intro i
    simp [M, tridiagonal, Fin.val_succ, Fin.ext_iff]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
    Fin.succ_zero_eq_one, Fin.val_one, pow_one]
  change d 0 * det (M.submatrix Fin.succ Fin.succ) +
    ((-1 : R) * M 0 1 * det (M.submatrix Fin.succ (1 : Fin (n + 2)).succAbove) +
      ∑ i : Fin n, (-1 : R) ^ (i.succ.succ.val) * M 0 i.succ.succ *
        det (M.submatrix Fin.succ i.succ.succ.succAbove)) = _
  rw [show M.submatrix Fin.succ Fin.succ = _ from tridiagonal_tail d, hcol]
  simp [hzero, M, tridiagonal, sub_eq_add_neg]

/-- Grounded path tail: diagonal z-2 except at its terminal vertex, z-1. -/
def pathTail (z : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  tridiagonal (fun i => if i.val + 1 = n then z - 1 else z - 2)

theorem num_characteristic_recurrence (z : R) (n : ℕ) :
    num z (n + 2) = (z - 2) * num z (n + 1) - num z n := by
  rw [show n + 2 = (n + 1) + 1 by omega, num_succ, den_succ, num_succ]
  ring

theorem pathTail_det_recurrence (z : R) (n : ℕ) :
    det (pathTail z (n + 2)) =
      (z - 2) * det (pathTail z (n + 1)) - det (pathTail z n) := by
  unfold pathTail
  rw [det_tridiagonal]
  simp only [Fin.val_zero, zero_add, show ¬1 = n + 2 by omega, ite_false]
  congr 2 <;> congr 1 <;> funext i <;>
    simp [Fin.val_succ, Nat.add_assoc, Nat.add_right_cancel_iff]

/-- The numerator recurrence is the determinant of the actual tridiagonal tail. -/
theorem pathTail_det (z : R) (n : ℕ) : det (pathTail z n) = num z (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pathTail]
  | one => simp [pathTail, tridiagonal]
  | more n ih ih' =>
    calc
      det (pathTail z (n + 2)) =
          (z - 2) * det (pathTail z (n + 1)) - det (pathTail z n) :=
        pathTail_det_recurrence z n
      _ = (z - 2) * num z (n + 2) - num z (n + 1) := by rw [ih, ih']
      _ = num z (n + 2 + 1) := (num_characteristic_recurrence z (n + 1)).symm

/-- The two terminal vertices of a nontrivial path have degree one; all others two. -/
theorem pathGraph_degree (n : ℕ) (i : Fin (n + 2)) :
    (SimpleGraph.pathGraph (n + 2)).degree i =
      if i.val = 0 ∨ i.val + 1 = n + 2 then 1 else 2 := by
  by_cases hi0 : i.val = 0
  · have hn : (SimpleGraph.pathGraph (n + 2)).neighborFinset i = {⟨1, by omega⟩} := by
      ext j
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj,
        Finset.mem_singleton, Fin.ext_iff]
      omega
    simp [SimpleGraph.degree, hn, hi0]
  · by_cases hilast : i.val + 1 = n + 2
    · have hn : (SimpleGraph.pathGraph (n + 2)).neighborFinset i = {⟨n, by omega⟩} := by
        ext j
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj,
          Finset.mem_singleton, Fin.ext_iff]
        omega
      simp [SimpleGraph.degree, hn, hilast]
    · let l : Fin (n + 2) := ⟨i.val - 1, by omega⟩
      let r : Fin (n + 2) := ⟨i.val + 1, by omega⟩
      have hlr : l ≠ r := by
        simp only [ne_eq, Fin.ext_iff, l, r]
        omega
      have hn : (SimpleGraph.pathGraph (n + 2)).neighborFinset i = {l, r} := by
        ext j
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj,
          Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, l, r]
        omega
      have hilast' : i.val ≠ n + 1 := by omega
      simp [SimpleGraph.degree, hn, hi0, hilast', hlr]

/-- The actual shifted graph Laplacian, not a recursively specified determinant. -/
def pathMatrix (z : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  z • (1 : Matrix (Fin n) (Fin n) R) - (SimpleGraph.pathGraph n).lapMatrix R

theorem pathMatrix_tridiagonal (z : R) (n : ℕ) :
    pathMatrix z (n + 2) = tridiagonal (fun i =>
      if i.val = 0 ∨ i.val + 1 = n + 2 then z - 1 else z - 2) := by
  ext i j
  simp only [pathMatrix, Matrix.sub_apply, Matrix.smul_apply,
    SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply]
  by_cases hij : i = j
  · subst j
    simp [tridiagonal, pathGraph_degree]
    split_ifs <;> rfl
  · simp [tridiagonal, hij, SimpleGraph.pathGraph_adj]

theorem pathMatrix_tail (z : R) (n : ℕ) :
    (pathMatrix z (n + 1)).submatrix Fin.succ Fin.succ = pathTail z n := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    rw [pathMatrix_tridiagonal, tridiagonal_tail]
    unfold pathTail
    congr 1
    funext i
    simp [Fin.val_succ, Nat.add_assoc, Nat.add_right_cancel_iff]

/-- Characteristic determinant of every nonempty path equals the scalar denominator. -/
theorem pathMatrix_det (z : R) (n : ℕ) :
    det (pathMatrix z (n + 1)) = den z (n + 1) := by
  cases n with
  | zero =>
    simp [pathMatrix, SimpleGraph.lapMatrix,
      SimpleGraph.degMatrix, SimpleGraph.degree, SimpleGraph.neighborFinset, den, state]
  | succ n =>
    rw [show n + 1 + 1 = n + 2 by omega, pathMatrix_tridiagonal, det_tridiagonal]
    have ht : tridiagonal (fun i : Fin (n + 1) =>
        if i.succ.val = 0 ∨ i.succ.val + 1 = n + 2 then z - 1 else z - 2) =
        pathTail z (n + 1) := by
      unfold pathTail
      congr 1
      funext i
      simp [Fin.val_succ, Nat.add_assoc, Nat.add_right_cancel_iff]
    have htt : tridiagonal (fun i : Fin n =>
        if i.succ.succ.val = 0 ∨ i.succ.succ.val + 1 = n + 2 then z - 1 else z - 2) =
        pathTail z n := by
      unfold pathTail
      congr 1
      funext i
      simp [Fin.val_succ, Nat.add_assoc]
    simp only [Fin.val_zero, true_or, ite_true, ht, htt, pathTail_det]
    rw [show n + 2 = (n + 1) + 1 by omega, den_succ]
    have h := num_succ z (n + 1)
    rw [show n + 1 + 1 = n + 2 by omega] at h
    linear_combination (z - 1) * h

variable {K : Type*} [Field K]

/-- Exact endpoint resolvent entry. Division follows Lean's total field convention;
the separately proved upper-half-plane nonvanishing will make it a genuine inverse. -/
theorem pathMatrix_inv_endpoint (z : K) (n : ℕ) :
    (pathMatrix z (n + 1))⁻¹ 0 0 = resolventQuotient z (n + 1) := by
  rw [Matrix.inv_def, Matrix.smul_apply,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul, Fin.succAbove_zero,
    pathMatrix_tail, pathTail_det, pathMatrix_det, Ring.inverse_eq_inv, smul_eq_mul]
  unfold resolventQuotient
  rw [div_eq_mul_inv, mul_comm]

#print axioms det_tridiagonal
#print axioms pathTail_det
#print axioms pathGraph_degree
#print axioms pathMatrix_tridiagonal
#print axioms pathMatrix_det
#print axioms pathMatrix_inv_endpoint

end Gebendorfer.RadenkovicGutman.PathRecurrence
