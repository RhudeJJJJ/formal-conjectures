import FormalConjectures.Paper.AouchicheHansenStevanovicSpectralRadiusRadius

/-! Full negative answer at order four, using the actual bag and objective.
The witness is the four-cycle. No corrected classification or infinite
even-handle improvement is asserted here. OpenAI Codex assisted with this proof. -/

namespace RadiusProductProof
open SimpleGraph Polynomial Matrix AouchicheHansenStevanovic.SpectralRadiusRadius
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def fourCycle : SimpleGraph (Fin 4) where
  Adj u v := u.val % 2 ≠ v.val % 2
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel fourCycle.Adj := fun u v =>
  inferInstanceAs (Decidable (u.val % 2 ≠ v.val % 2))

theorem edist_fourCycle (u v : Fin 4) :
    fourCycle.edist u v = if u = v then 0 else if fourCycle.Adj u v then 1 else 2 := by
  by_cases h : u = v
  · subst v
    simp
  · rw [if_neg h]
    by_cases ha : fourCycle.Adj u v
    · rw [if_pos ha, SimpleGraph.edist_eq_one_iff_adj.mpr ha]
    · rw [if_neg ha]
      apply SimpleGraph.edist_eq_two_iff.mpr
      refine ⟨h, ha, ?_⟩
      have hex : ∀ a b : Fin 4, a ≠ b → ¬fourCycle.Adj a b →
          ∃ c, fourCycle.Adj a c ∧ fourCycle.Adj c b := by decide
      obtain ⟨c, hc, hv⟩ := hex u v h ha
      refine ⟨c, ?_⟩
      change fourCycle.Adj u c ∧ fourCycle.Adj v c
      exact ⟨hc, hv.symm⟩

theorem fourCycle_connected : fourCycle.Connected := by
  refine ⟨fun u v => ?_⟩
  apply SimpleGraph.reachable_of_edist_ne_top
  rw [edist_fourCycle]
  split_ifs <;> norm_num

theorem radius_fourCycle : fourCycle.radius = 2 := by
  have he : ∀ u, fourCycle.eccent u = 2 := by
    intro u
    apply le_antisymm
    · apply iSup_le
      intro v
      rw [edist_fourCycle]
      split_ifs <;> norm_num
    · have hex : ∀ a : Fin 4, ∃ b, a ≠ b ∧ ¬fourCycle.Adj a b := by decide
      obtain ⟨v, hv, ha⟩ := hex u
      have hd : fourCycle.edist u v = 2 := by rw [edist_fourCycle, if_neg hv, if_neg ha]
      rw [← hd]
      exact SimpleGraph.edist_le_eccent
  simp [SimpleGraph.radius, he]

theorem bag_four : bag (4 / 2 + 2) ((4 + 1) / 2) = (⊤ : SimpleGraph (Fin 4)) := by
  ext u v
  change (u ≠ v ∧ _) ↔ u ≠ v
  fin_cases u <;> fin_cases v <;> decide

def cycleMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,1,0,1; 1,0,1,0; 0,1,0,1; 1,0,1,0]
def completeMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,1,1,1; 1,0,1,1; 1,1,0,1; 1,1,1,0]

theorem actual_cycle_matrix [d : DecidableRel fourCycle.Adj] : fourCycle.adjMatrix ℝ = cycleMatrix := by
  ext u v
  fin_cases u <;> fin_cases v <;> norm_num [SimpleGraph.adjMatrix, fourCycle, cycleMatrix]

theorem actual_complete_matrix [d : DecidableRel (⊤ : SimpleGraph (Fin 4)).Adj] : (⊤ : SimpleGraph (Fin 4)).adjMatrix ℝ = completeMatrix := by
  ext u v
  fin_cases u <;> fin_cases v <;> norm_num [SimpleGraph.adjMatrix, completeMatrix]

def basis : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,1,1; 1,-1,1,-1; 1,1,-1,-1; 1,-1,-1,1]
noncomputable def inverseBasis : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/4,1/4,1/4,1/4; 1/4,-1/4,1/4,-1/4;
     1/4,1/4,-1/4,-1/4; 1/4,-1/4,-1/4,1/4]
def cycleDiagonal : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![2,-2,0,0]
def completeDiagonal : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![3,-1,-1,-1]

theorem basis_right_inverse : basis * inverseBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, basis, inverseBasis,
      Matrix.one_apply, Fin.ext_iff]
theorem basis_left_inverse : inverseBasis * basis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, basis, inverseBasis,
      Matrix.one_apply, Fin.ext_iff]

theorem cycle_intertwines : cycleMatrix * basis = basis * cycleDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, basis, cycleMatrix,
      cycleDiagonal, Matrix.diagonal, Fin.ext_iff]
theorem complete_intertwines : completeMatrix * basis = basis * completeDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, basis, completeMatrix,
      completeDiagonal, Matrix.diagonal, Fin.ext_iff]

theorem charpoly_of_intertwines (A D : Matrix (Fin 4) (Fin 4) ℝ)
    (h : A * basis = basis * D) : A.charpoly = D.charpoly := by
  have he : A = basis * D * inverseBasis := by
    calc
      A = A * (basis * inverseBasis) := by rw [basis_right_inverse, mul_one]
      _ = (A * basis) * inverseBasis := (mul_assoc _ _ _).symm
      _ = basis * D * inverseBasis := by rw [h]
  calc
    A.charpoly = (basis * D * inverseBasis).charpoly := congrArg Matrix.charpoly he
    _ = (inverseBasis * (basis * D)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = D.charpoly := by rw [← mul_assoc, basis_left_inverse, one_mul]

theorem cycle_charpoly : cycleMatrix.charpoly = X^2 * (X - 2) * (X + 2) := by
  rw [charpoly_of_intertwines _ _ cycle_intertwines]
  simp [cycleDiagonal, Matrix.charpoly_diagonal, Fin.prod_univ_succ]
  <;> ring
theorem complete_charpoly : completeMatrix.charpoly = (X - 3) * (X + 1)^3 := by
  rw [charpoly_of_intertwines _ _ complete_intertwines]
  simp [completeDiagonal, Matrix.charpoly_diagonal, Fin.prod_univ_succ]
  <;> ring

theorem cycle_spectral_sup : sSup (spectrum ℝ cycleMatrix) = 2 := by
  have hm : (2 : ℝ) ∈ spectrum ℝ cycleMatrix := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, cycle_charpoly]
    norm_num [Polynomial.IsRoot]
  have hle : ∀ x ∈ spectrum ℝ cycleMatrix, x ≤ 2 := by
    intro x hx
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, cycle_charpoly] at hx
    have he : x^2 * (x - 2) * (x + 2) = 0 := by simpa [Polynomial.IsRoot] using hx
    rcases mul_eq_zero.mp he with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · have : x = 0 := eq_zero_of_pow_eq_zero hz
        linarith
      · linarith
    · linarith
  exact le_antisymm (csSup_le ⟨2, hm⟩ hle) (le_csSup ⟨2, hle⟩ hm)

theorem complete_spectral_sup : sSup (spectrum ℝ completeMatrix) = 3 := by
  have hm : (3 : ℝ) ∈ spectrum ℝ completeMatrix := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, complete_charpoly]
    norm_num [Polynomial.IsRoot]
  have hle : ∀ x ∈ spectrum ℝ completeMatrix, x ≤ 3 := by
    intro x hx
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, complete_charpoly] at hx
    have he : (x - 3) * (x + 1)^3 = 0 := by simpa [Polynomial.IsRoot] using hx
    rcases mul_eq_zero.mp he with hz | hz
    · linarith
    · have : x + 1 = 0 := eq_zero_of_pow_eq_zero hz
      linarith
  exact le_antisymm (csSup_le ⟨3, hm⟩ hle) (le_csSup ⟨3, hle⟩ hm)

theorem conjecture4_4 : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    3 ≤ n → G.Connected → objective G ≤ objective (bag (n / 2 + 2) ((n + 1) / 2)) := by
  classical
  intro h
  have hh := h 4 fourCycle (by norm_num) fourCycle_connected
  have hr : (⊤ : SimpleGraph (Fin 4)).radius = 1 := by
    simp [SimpleGraph.radius, SimpleGraph.eccent_top]
  rw [bag_four] at hh
  simp only [objective] at hh
  rw [actual_cycle_matrix (d := Classical.decRel _),
    actual_complete_matrix (d := Classical.decRel _), cycle_spectral_sup,
    complete_spectral_sup, radius_fourCycle, hr] at hh
  norm_num at hh

end RadiusProductProof
#print axioms RadiusProductProof.conjecture4_4
#print axioms RadiusProductProof.cycle_spectral_sup
#print axioms RadiusProductProof.radius_fourCycle
