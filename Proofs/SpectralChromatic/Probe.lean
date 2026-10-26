module

public import Lean.Util.CollectAxioms

public import FormalConjectures.Paper.AouchicheHansenStevanovicSpectralChromatic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Exact counterexample to the submitted spectral-chromatic table candidate

The actual Mathlib graphs `turanGraph 5 2` and `turanGraph 5 3` have objectives
`sqrt 6 - 2` and `sqrt 5 - 2`, respectively. We compute determinants of their
actual adjacency matrices, identify the largest real spectral values, and check
proper colorings and cliques. This proves the original negative declaration.
It does not prove the corrected universal optimizer or its equality cases.

Source: J. J. Gebendorfer, *Maximizing the Difference Between the Spectral Radius
and the Chromatic Number*, 7 August 2026, the explicit order-five comparison in
Section 3 of the source package linked by the original statement module.
-/

@[expose] public section

namespace AouchicheHansenStevanovic.SpectralChromatic

open SimpleGraph Matrix

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem determinant_turan_five_two (x : ℝ) :
    (Matrix.scalar (Fin 5) x - (turanGraph 5 2).adjMatrix ℝ).det =
      x^3 * (x^2 - 6) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_one,
    Matrix.submatrix_apply, SimpleGraph.adjMatrix, SimpleGraph.turanGraph,
    Matrix.scalar, Matrix.diagonal, Fin.succAbove]
  <;> ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem determinant_turan_five_three (x : ℝ) :
    (Matrix.scalar (Fin 5) x - (turanGraph 5 3).adjMatrix ℝ).det =
      x^2 * (x + 2) * (x^2 - 2*x - 4) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_one,
    Matrix.submatrix_apply, SimpleGraph.adjMatrix, SimpleGraph.turanGraph,
    Matrix.scalar, Matrix.diagonal, Fin.succAbove]
  <;> ring

theorem mem_spectrum_turan_five_two (x : ℝ) :
    x ∈ spectrum ℝ ((turanGraph 5 2).adjMatrix ℝ) ↔ x^3 * (x^2 - 6) = 0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, Matrix.eval_charpoly,
    determinant_turan_five_two]

theorem mem_spectrum_turan_five_three (x : ℝ) :
    x ∈ spectrum ℝ ((turanGraph 5 3).adjMatrix ℝ) ↔
      x^2 * (x + 2) * (x^2 - 2*x - 4) = 0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, Matrix.eval_charpoly,
    determinant_turan_five_three]

theorem rho_turan_five_two : rho (turanGraph 5 2) = Real.sqrt 6 := by
  have hs : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hm : Real.sqrt 6 ∈ spectrum ℝ ((turanGraph 5 2).adjMatrix ℝ) := by
    rw [mem_spectrum_turan_five_two, hs]; ring
  have hu : ∀ x ∈ spectrum ℝ ((turanGraph 5 2).adjMatrix ℝ), x ≤ Real.sqrt 6 := by
    intro x hx
    rcases mul_eq_zero.mp ((mem_spectrum_turan_five_two x).1 hx) with h | h
    · have : x = 0 := pow_eq_zero h
      simpa [this] using hp
    · by_contra hn
      have hl : Real.sqrt 6 < x := lt_of_not_ge hn
      nlinarith [sq_nonneg (x - Real.sqrt 6)]
  exact le_antisymm (csSup_le ⟨_, hm⟩ hu) (le_csSup ⟨_, hu⟩ hm)

theorem rho_turan_five_three : rho (turanGraph 5 3) = 1 + Real.sqrt 5 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hm : 1 + Real.sqrt 5 ∈ spectrum ℝ ((turanGraph 5 3).adjMatrix ℝ) := by
    apply (mem_spectrum_turan_five_three _).2
    have he : (1 + Real.sqrt 5)^2 - 2*(1 + Real.sqrt 5) - 4 = 0 := by nlinarith
    rw [he, mul_zero]
  have hu : ∀ x ∈ spectrum ℝ ((turanGraph 5 3).adjMatrix ℝ), x ≤ 1 + Real.sqrt 5 := by
    intro x hx
    rcases mul_eq_zero.mp ((mem_spectrum_turan_five_three x).1 hx) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · have : x = 0 := pow_eq_zero h
        simpa [this] using (by linarith : (0 : ℝ) ≤ 1 + Real.sqrt 5)
      · linarith
    · by_contra hn
      have hl : 1 + Real.sqrt 5 < x := lt_of_not_ge hn
      nlinarith [sq_nonneg (x - (1 + Real.sqrt 5))]
  exact le_antisymm (csSup_le ⟨_, hm⟩ hu) (le_csSup ⟨_, hu⟩ hm)

def residueColoring (n r : ℕ) (hr : 0 < r) : (turanGraph n r).Coloring (Fin r) where
  toFun v := ⟨v.val % r, Nat.mod_lt _ hr⟩
  map_rel' := by
    intro v w hvw
    change (⟨v.val % r, Nat.mod_lt _ hr⟩ : Fin r) ≠ ⟨w.val % r, Nat.mod_lt _ hr⟩
    intro h
    exact hvw (congrArg Fin.val h)

theorem chromatic_turan_five_two : (turanGraph 5 2).chromaticNumber = 2 := by
  apply le_antisymm (residueColoring 5 2 (by decide)).colorable.chromaticNumber_le
  exact two_le_chromaticNumber_of_adj (G := turanGraph 5 2)
    (u := 0) (v := 1) (by decide)

theorem chromatic_turan_five_three : (turanGraph 5 3).chromaticNumber = 3 := by
  apply le_antisymm (residueColoring 5 3 (by decide)).colorable.chromaticNumber_le
  apply le_chromaticNumber_of_pairwise_adj (ι := Fin 3) (by simp)
    (fun i => (⟨i.val, by omega⟩ : Fin 5))
  intro i j hij
  change i.val % 3 ≠ j.val % 3
  simpa only [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt, Fin.val_inj] using hij

theorem connected_turan_five_two : (turanGraph 5 2).Connected := by
  refine ⟨fun u v => ?_⟩
  by_cases h : (turanGraph 5 2).Adj u v
  · exact h.reachable
  · by_cases hu : u.val % 2 = 0
    · exact (show (turanGraph 5 2).Adj u 1 by
        simpa [turanGraph, hu]).reachable.trans
          (show (turanGraph 5 2).Adj 1 v by
            change (1 : ℕ) % 2 ≠ v.val % 2
            change ¬ u.val % 2 ≠ v.val % 2 at h
            omega).reachable
    · exact (show (turanGraph 5 2).Adj u 0 by
        simpa [turanGraph] using hu).reachable.trans
          (show (turanGraph 5 2).Adj 0 v by
            change (0 : ℕ) % 2 ≠ v.val % 2
            change ¬ u.val % 2 ≠ v.val % 2 at h
            omega).reachable

theorem ceil_sqrt_five : ⌈Real.sqrt (5 : ℝ)⌉₊ = 3 := by
  rw [Nat.ceil_eq_iff (by decide : (3 : ℕ) ≠ 0)]
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  constructor <;> norm_num <;> nlinarith

theorem objective_turan_five_two : objective (turanGraph 5 2) = Real.sqrt 6 - 2 := by
  simp [objective, rho_turan_five_two, chromatic_turan_five_two]

theorem objective_turan_five_three : objective (turanGraph 5 3) = Real.sqrt 5 - 2 := by
  simp [objective, rho_turan_five_three, chromatic_turan_five_three]
  <;> ring

theorem strict_five_vertex_comparison :
    objective (turanGraph 5 3) < objective (turanGraph 5 2) := by
  rw [objective_turan_five_three, objective_turan_five_two]
  have h : Real.sqrt (5 : ℝ) < Real.sqrt 6 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- Full proof of the exact negative declaration in the original PR. -/
theorem full_table1_upper : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj], 3 ≤ n → G.Connected →
    objective G ≤ objective (turanGraph n (⌈Real.sqrt n⌉₊)) := by
  intro h
  have hf := h 5 (turanGraph 5 2) (by decide) connected_turan_five_two
  rw [ceil_sqrt_five] at hf
  exact (not_le_of_gt strict_five_vertex_comparison) hf

end AouchicheHansenStevanovic.SpectralChromatic


/-! Exact original-type equality and transitive axiom checks. -/

open Lean Meta Elab Command in
run_elab do
  let original := `AouchicheHansenStevanovic.SpectralChromatic.table1_upper
  let certificate := `AouchicheHansenStevanovic.SpectralChromatic.full_table1_upper
  let oi ← getConstInfo original
  let ci ← getConstInfo certificate
  unless oi.levelParams.length == ci.levelParams.length do
    throwError "Universe-parameter mismatch"
  let levels := oi.levelParams.map Level.param
  unless ← isDefEq (← inferType (mkConst original levels))
      (← inferType (mkConst certificate levels)) do
    throwError "Full target type differs from original"
  logInfo m!"EXACT TYPE: {original} = {certificate}"

#print axioms AouchicheHansenStevanovic.SpectralChromatic.full_table1_upper
#print axioms AouchicheHansenStevanovic.SpectralChromatic.table1_upper
