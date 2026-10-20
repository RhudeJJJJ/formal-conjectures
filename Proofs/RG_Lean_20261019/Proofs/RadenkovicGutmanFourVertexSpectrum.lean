/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallOrders
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Exact Laplacian energies at the first nonpath order

The actual four-vertex path has energy 2 + 2 sqrt(2), and the actual
four-vertex star has energy 5, centered at mean degree 3/2. Characteristic
polynomial roots retain every multiplicity. The comparison is strict.
-/

namespace Gebendorfer.RadenkovicGutman.FourVertexSpectrum

open SimpleGraph Matrix Polynomial GlobalAssembly
open scoped Classical
noncomputable section

def starFour : SimpleGraph (Fin 4) := starGraph 0

theorem energy_eq_roots (G : SimpleGraph (Fin 4)) :
    laplacianEnergy G =
      ((G.lapMatrix ℝ).charpoly.roots.map (fun x => |x - meanDegree G|)).sum := by
  unfold laplacianEnergy centredEnergy
  exact IsoEnergy.spectral_sum_roots G (fun x => |x - meanDegree G|)

theorem starFour_lapMatrix : starFour.lapMatrix ℝ =
    !![3, -1, -1, -1; -1, 1, 0, 0; -1, 0, 1, 0; -1, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [starFour, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply,
      degree_starGraph_center, degree_starGraph_of_ne_center]

theorem starFour_charpoly : (starFour.lapMatrix ℝ).charpoly =
    X * (X - 1) ^ 2 * (X - 4) := by
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly, starFour_lapMatrix, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.scalar_apply,
    Matrix.submatrix_apply, Matrix.diagonal_apply]
  <;> ring

theorem pathFour_charpoly : ((pathGraph 4).lapMatrix ℝ).charpoly =
    X * (X - 2) * (X ^ 2 - 4 * X + 2) := by
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly]
  have hd : (Matrix.scalar (Fin 4) x - (pathGraph 4).lapMatrix ℝ).det =
      PathRecurrence.den x 4 := by
    simpa only [PathRecurrence.pathMatrix, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal] using PathRecurrence.pathMatrix_det x 3
  rw [hd]
  norm_num [PathRecurrence.den, PathRecurrence.state]
  <;> ring

theorem starFour_roots : (starFour.lapMatrix ℝ).charpoly.roots =
    (([0, 1, 1, 4] : List ℝ) : Multiset ℝ) := by
  have hf : (starFour.lapMatrix ℝ).charpoly =
      ((([0, 1, 1, 4] : List ℝ) : Multiset ℝ).map (fun r => X - C r)).prod := by
    rw [starFour_charpoly]
    norm_num
    <;> ring
  rw [hf, Polynomial.roots_multiset_prod_X_sub_C]

theorem pathFour_roots : ((pathGraph 4).lapMatrix ℝ).charpoly.roots =
    (([0, 2 - Real.sqrt 2, 2, 2 + Real.sqrt 2] : List ℝ) : Multiset ℝ) := by
  have hs : (C (Real.sqrt 2) : ℝ[X]) ^ 2 = 2 := by
    rw [← Polynomial.C_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hf : ((pathGraph 4).lapMatrix ℝ).charpoly =
      ((([0, 2 - Real.sqrt 2, 2, 2 + Real.sqrt 2] : List ℝ) : Multiset ℝ).map
        (fun r => X - C r)).prod := by
    rw [pathFour_charpoly]
    norm_num [Polynomial.C_sub, Polynomial.C_add]
    linear_combination X * (X - 2) * hs
  rw [hf, Polynomial.roots_multiset_prod_X_sub_C]

theorem starFour_meanDegree : meanDegree starFour = 3 / 2 := by
  have h := tree_meanDegree (G := starFour) (isTree_starGraph (0 : Fin 4))
  norm_num at h
  exact h

theorem pathFour_meanDegree : meanDegree (pathGraph 4) = 3 / 2 := by
  have hd (i : Fin 4) := PathRecurrence.pathGraph_degree 2 i
  have hs := (pathGraph 4).sum_degrees_eq_twice_card_edges
  norm_num [Fin.sum_univ_succ, hd] at hs
  have he : (pathGraph 4).edgeFinset.card = 3 := by omega
  norm_num [meanDegree, he]

theorem starFour_energy : laplacianEnergy starFour = 5 := by
  rw [energy_eq_roots, starFour_roots, starFour_meanDegree]
  norm_num

theorem pathFour_energy : laplacianEnergy (pathGraph 4) = 2 + 2 * Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have ha : 2 - Real.sqrt 2 - (3 / 2 : ℝ) ≤ 0 := by nlinarith
  have hb : 0 ≤ 2 + Real.sqrt 2 - (3 / 2 : ℝ) := by nlinarith
  rw [energy_eq_roots, pathFour_roots, pathFour_meanDegree]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [abs_of_nonpos ha, abs_of_nonneg hb]
  norm_num
  <;> ring

theorem pathFour_energy_lt_starFour : laplacianEnergy (pathGraph 4) <
    laplacianEnergy starFour := by
  rw [pathFour_energy, starFour_energy]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

#check @Matrix.IsHermitian.roots_charpoly_eq_eigenvalues
#check @Polynomial.roots_multiset_prod_X_sub_C
#check @pathFour_energy_lt_starFour

#print axioms energy_eq_roots
#print axioms starFour_lapMatrix
#print axioms starFour_charpoly
#print axioms pathFour_charpoly
#print axioms starFour_roots
#print axioms pathFour_roots
#print axioms starFour_meanDegree
#print axioms pathFour_meanDegree
#print axioms starFour_energy
#print axioms pathFour_energy
#print axioms pathFour_energy_lt_starFour

end
end Gebendorfer.RadenkovicGutman.FourVertexSpectrum
