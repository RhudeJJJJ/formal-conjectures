import FormalConjectures.Arxiv.«2601.18071».GreenEigenvalue

/-! A six-face counterexample to Knill's Question B: the unfilled triangle.
It is the C3 member explicitly described in Gebendorfer's odd-cycle manuscript,
issue7256. It is connected but is not a flag complex. We prove that its largest
algebraic Green eigenvalue has multiplicity at least two; this suffices for the
universal negative answer. No minimum-order or whole-family claim is made.
OpenAI Codex assisted with formalization and validation. -/

namespace KnillGreenProof
open Matrix Polynomial Knill.GreenEigenvalue
set_option maxRecDepth 100000
set_option maxHeartbeats 300000

def triangle : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s.card ≤ 2}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, (Finset.card_le_card hts).trans hs.2⟩

def faceSet : Fin 6 → Finset (Fin 3) := ![{0}, {1}, {2}, {0, 1}, {1, 2}, {0, 2}]
abbrev Face := {s : Finset (Fin 3) // s ∈ triangle}

def indexedFace (i : Fin 6) : Face := ⟨faceSet i, by
  change (faceSet i).Nonempty ∧ (faceSet i).card ≤ 2
  fin_cases i <;> decide⟩

noncomputable def faceEquiv : Fin 6 ≃ Face := Equiv.ofBijective indexedFace (by
  constructor
  · intro i j hij
    have hv := congrArg Subtype.val hij
    have hinj : ∀ i j : Fin 6, faceSet i = faceSet j → i = j := by decide
    exact hinj i j hv
  · intro s
    have hall : ∀ S : Finset (Fin 3), S.Nonempty ∧ S.card ≤ 2 →
        ∃ i : Fin 6, faceSet i = S := by decide
    obtain ⟨i, hi⟩ := hall s.val s.property
    exact ⟨i, Subtype.ext hi⟩)

def connection : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,0,0,1,0,1; 0,1,0,1,1,0; 0,0,1,0,1,1;
     1,1,0,1,1,1; 0,1,1,1,1,1; 1,0,1,1,1,1]

def green : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-1,-1,-1,1,0,1; -1,-1,-1,1,1,0; -1,-1,-1,0,1,1;
     1,1,0,-1,0,0; 0,1,1,0,-1,0; 1,0,1,0,0,-1]

theorem actual_connection :
    Matrix.reindex faceEquiv.symm faceEquiv.symm (connectionMatrix 3 triangle) =
      connection := by
  ext i j
  change (if Disjoint (faceSet i) (faceSet j) then (0 : ℝ) else 1) = connection i j
  fin_cases i <;> fin_cases j <;> norm_num [faceSet, connection]

theorem inverse_connection : connection⁻¹ = green := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [connection, green, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem green_charpoly :
    green.charpoly = (X^2 + 4*X - 1) * (X^2 + X - 1)^2 := by
  norm_num [green, Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero,
    Matrix.det_fin_zero, Fin.sum_univ_succ, Matrix.submatrix]
  <;> ring

noncomputable def largest : ℝ := (Real.sqrt 5 - 1) / 2

theorem largest_positive : 0 < largest := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  dsimp [largest]
  nlinarith

theorem largest_root : largest^2 + largest - 1 = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [largest]
  nlinarith

theorem largest_in_spectrum : largest ∈ spectrum ℝ green := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, green_charpoly]
  simp [Polynomial.IsRoot, largest_root]

theorem spectrum_le_largest : ∀ x ∈ spectrum ℝ green, x ≤ largest := by
  intro x hx
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, green_charpoly] at hx
  have he : (x^2 + 4*x - 1) * (x^2 + x - 1)^2 = 0 := by
    simpa [Polynomial.IsRoot] using hx
  have hr := largest_root
  have hp := largest_positive
  by_contra hn
  have hlt : largest < x := lt_of_not_ge hn
  rcases mul_eq_zero.mp he with he | he
  · nlinarith [sq_nonneg (x - largest)]
  · have he' : x^2 + x - 1 = 0 := pow_eq_zero he
    nlinarith [sq_nonneg (x - largest)]

theorem spectral_sup : sSup (spectrum ℝ green) = largest := by
  have hne : (spectrum ℝ green).Nonempty := ⟨largest, largest_in_spectrum⟩
  have hb : BddAbove (spectrum ℝ green) := ⟨largest, spectrum_le_largest⟩
  exact le_antisymm (csSup_le hne spectrum_le_largest) (le_csSup hb largest_in_spectrum)

theorem green_multiplicity : 2 ≤ green.charpoly.rootMultiplicity largest := by
  apply (Polynomial.le_rootMultiplicity_iff green.charpoly_monic.ne_zero).2
  have hd : (X - C largest : ℝ[X]) ∣ X^2 + X - 1 := by
    rw [Polynomial.dvd_iff_isRoot]
    simpa [Polynomial.IsRoot] using largest_root
  rw [green_charpoly]
  exact (pow_dvd_pow_of_dvd hd 2).trans (dvd_mul_left _ _)

theorem questionB : ¬ ∀ (n : ℕ) (K : PreAbstractSimplicialComplex (Fin n)),
    K.faces.Nonempty → maximalMultiplicity n K = 1 := by
  classical
  intro h
  have hn : triangle.faces.Nonempty := by
    refine ⟨{0}, ?_⟩
    change (Finset.Nonempty ({0} : Finset (Fin 3))) ∧
      ({0} : Finset (Fin 3)).card ≤ 2
    decide
  have hh := h 3 triangle hn
  letI := Fintype.ofFinite Face
  have hg : Matrix.reindex faceEquiv.symm faceEquiv.symm
      (connectionMatrix 3 triangle)⁻¹ = green := by
    rw [← Matrix.inv_reindex, actual_connection, inverse_connection]
  have hp : ((connectionMatrix 3 triangle)⁻¹).charpoly = green.charpoly := by
    rw [← Matrix.charpoly_reindex faceEquiv.symm, hg]
  have hspec : spectrum ℝ ((connectionMatrix 3 triangle)⁻¹) = spectrum ℝ green := by
    ext x
    simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, hp]
  have hm := green_multiplicity
  change ((connectionMatrix 3 triangle)⁻¹).charpoly.rootMultiplicity
    (sSup (spectrum ℝ ((connectionMatrix 3 triangle)⁻¹))) = 1 at hh
  rw [hp, hspec, spectral_sup] at hh
  omega

end KnillGreenProof

#print axioms KnillGreenProof.actual_connection
#print axioms KnillGreenProof.green_charpoly
#print axioms KnillGreenProof.green_multiplicity
#print axioms KnillGreenProof.questionB
