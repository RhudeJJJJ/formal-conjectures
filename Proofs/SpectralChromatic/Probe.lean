module
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

/-! # API and exact determinant diagnostic for the five-vertex witness -/
@[expose] public section
open SimpleGraph Matrix

#check Matrix.eval_charpoly
#check Matrix.mem_spectrum_iff_isRoot_charpoly
#check SimpleGraph.Connected
#check SimpleGraph.Preconnected
#check SimpleGraph.Adj.reachable
#check SimpleGraph.Reachable.trans
#check SimpleGraph.le_chromaticNumber_of_pairwise_adj
#check SimpleGraph.Colorable.chromaticNumber_le
#check ENat.toNat_le_toNat
#check ENat.toNat_le_of_le_coe
#check ENat.coe_toNat
#check Real.sqrt_sq_eq_abs
#check Nat.ceil_eq_iff
#check Real.sqrt_le_iff
#check Real.lt_sqrt

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem det_two (x : ℝ) :
    ((x • (1 : Matrix (Fin 5) (Fin 5) ℝ)) - (turanGraph 5 2).adjMatrix ℝ).det =
      x^3 * (x^2 - 6) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_one,
    Matrix.submatrix_apply, SimpleGraph.adjMatrix, SimpleGraph.turanGraph,
    Matrix.smul_apply, Matrix.one_apply, Fin.succAbove]
  <;> ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem det_three (x : ℝ) :
    ((x • (1 : Matrix (Fin 5) (Fin 5) ℝ)) - (turanGraph 5 3).adjMatrix ℝ).det =
      x^2 * (x + 2) * (x^2 - 2*x - 4) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_one,
    Matrix.submatrix_apply, SimpleGraph.adjMatrix, SimpleGraph.turanGraph,
    Matrix.smul_apply, Matrix.one_apply, Fin.succAbove]
  <;> ring
