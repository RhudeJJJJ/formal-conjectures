module

public import Proofs.JiaSong.Geometry

/-! # Complete ordered distance spectrum of the actual bowtie

We compute the characteristic polynomial of the graph distance matrix, then
sort all its roots with algebraic multiplicities. In particular the second
eigenvalue is the original antitone enumeration's position one.
-/

@[expose] public section
namespace JiaSong.Certificate
open Matrix Polynomial

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem determinant (x : ℝ) :
    (Matrix.scalar (Fin 5) x - distanceMatrix H).det =
      (x + 1)^2 * (x + 3) * (x^2 - 5*x - 4) := by
  rw [distance_matrix]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Matrix.scalar, Matrix.diagonal,
    Matrix.vecHead, Matrix.vecTail, Fin.succAbove]
  ring

noncomputable def upperRoot : ℝ := (5 + Real.sqrt 41) / 2
noncomputable def lowerRoot : ℝ := (5 - Real.sqrt 41) / 2

noncomputable def spectrumList : List ℝ :=
  [upperRoot, lowerRoot, -1, -1, -3]

theorem quadratic_factor (x : ℝ) :
    (x - upperRoot) * (x - lowerRoot) = x^2 - 5*x - 4 := by
  have hs : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  dsimp [upperRoot, lowerRoot]
  nlinarith

theorem charpoly_split : (distanceMatrix H).charpoly =
    (spectrumList.map fun r => (X - C r : ℝ[X])).prod := by
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly, determinant]
  simp only [spectrumList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one]
  calc
    (x + 1)^2 * (x + 3) * (x^2 - 5*x - 4) =
        (x - upperRoot) * (x - lowerRoot) * (x + 1) * (x + 1) * (x + 3) := by
      rw [quadratic_factor]
      ring
    _ = _ := by ring

theorem roots : (distanceMatrix H).charpoly.roots = (spectrumList : Multiset ℝ) := by
  rw [charpoly_split]
  simpa using Polynomial.roots_multiset_prod_X_sub_C (spectrumList : Multiset ℝ)

theorem spectrumList_pairwise : spectrumList.Pairwise (· ≥ ·) := by
  have hs : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have hp := Real.sqrt_nonneg (41 : ℝ)
  have hu : Real.sqrt 41 < 7 := by nlinarith
  norm_num [spectrumList, upperRoot, lowerRoot, List.pairwise_cons] <;>
    (repeat' constructor <;> linarith)

theorem ordered_spectrum (h : (distanceMatrix H).IsHermitian) :
    List.ofFn h.eigenvalues₀ = spectrumList := by
  rw [← h.sort_roots_charpoly_eq_eigenvalues₀, roots]
  change (spectrumList : Multiset ℝ).sort (· ≥ ·) = spectrumList
  rw [Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simpa only [decide_eq_true_eq] using spectrumList_pairwise

theorem second_eigenvalue : secondDistanceEigenvalue H = lowerRoot := by
  let h : (distanceMatrix H).IsHermitian := by
    apply Matrix.ext
    intro i j
    simp [Matrix.conjTranspose_apply, distanceMatrix, SimpleGraph.dist_comm]
  change (List.ofFn h.eigenvalues₀).getD 1 0 = lowerRoot
  rw [ordered_spectrum h]
  rfl

end JiaSong.Certificate
