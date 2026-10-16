import FormalConjectures.Arxiv.«2202.00325».DegreeDispersion

/-! Complete proofs of Clark Conjecture 2 and its star equality case.
The proof uses degrees in [1,n-1], the degree sum and a nonnegative square.
It is an alternative bounded-variance argument for Theorem 2.1 of
Gebendorfer's cited manuscript, rather than a line-by-line formalization of
its edge-pair defect identity. No claim about Conjecture 3 is made.
OpenAI Codex assisted with formalization. -/

namespace DegreeDispersionProof
open SimpleGraph Finset Clark.DegreeDispersion

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def slack : ℝ :=
  ∑ v : V, ((G.degree v : ℝ) - 1) * ((Fintype.card V : ℝ) - 1 - G.degree v)

omit [DecidableEq V] in
theorem degree_sum : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem slack_identity :
    slack G = 2 * (Fintype.card V : ℝ) * G.edgeFinset.card -
      (∑ v : V, (G.degree v : ℝ)^2) -
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
  have ht (v : V) : ((G.degree v : ℝ) - 1) *
      ((Fintype.card V : ℝ) - 1 - G.degree v) =
      (Fintype.card V : ℝ) * G.degree v - (G.degree v : ℝ)^2 -
        ((Fintype.card V : ℝ) - 1) := by ring
  simp only [slack, ht, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  rw [degree_sum]
  ring

theorem defect_identity (hn : 2 ≤ Fintype.card V) (hm : 0 < G.edgeFinset.card) :
    ((Fintype.card V : ℝ) - 2)^2 / (4 * ((Fintype.card V : ℝ) - 1)) -
      dispersion G =
    (Fintype.card V : ℝ) * slack G / (4 * (G.edgeFinset.card : ℝ)^2) +
      (Fintype.card V : ℝ)^2 * ((G.edgeFinset.card : ℝ) - Fintype.card V + 1)^2 /
        (4 * (G.edgeFinset.card : ℝ)^2 * ((Fintype.card V : ℝ) - 1)) := by
  have hn' : (Fintype.card V : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hm' : (G.edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [dispersion, slack_identity]
  field_simp [hn', hm']
  ring

omit [DecidableEq V] in
theorem degree_positive (hG : G.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    1 ≤ G.degree v := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have := hG.preconnected.degree_pos_of_nontrivial v
  omega

theorem edge_positive (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    0 < G.edgeFinset.card := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice inferInstance
  have hp := degree_positive G hG hn v
  have hb := G.degree_le_card_edgeFinset (v := v)
  omega

theorem slack_nonneg (hG : G.Connected) (hn : 2 ≤ Fintype.card V) : 0 ≤ slack G := by
  apply sum_nonneg
  intro v _
  have hp := degree_positive G hG hn v
  have hb := G.degree_lt_card_verts v
  have hp' : 0 ≤ (G.degree v : ℝ) - 1 := by
    have : (1 : ℝ) ≤ G.degree v := by exact_mod_cast hp
    linarith
  have hb' : 0 ≤ (Fintype.card V : ℝ) - 1 - G.degree v := by
    have : (G.degree v : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast (by omega : G.degree v + 1 ≤ Fintype.card V)
    linarith
  exact mul_nonneg hp' hb'

theorem conjecture2 (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    dispersion G ≤ ((Fintype.card V : ℝ) - 2)^2 /
      (4 * ((Fintype.card V : ℝ) - 1)) := by
  have hid := defect_identity G hn (edge_positive G hG hn)
  have hs := slack_nonneg G hG hn
  have hnr : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by linarith
  have hmr : (0 : ℝ) < G.edgeFinset.card := by exact_mod_cast edge_positive G hG hn
  have hdef : 0 ≤ ((Fintype.card V : ℝ) - 2)^2 / (4 * ((Fintype.card V : ℝ) - 1)) - dispersion G := by
    rw [hid]
    positivity
  linarith

theorem equality_data (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (he : dispersion G = ((Fintype.card V : ℝ) - 2)^2 /
      (4 * ((Fintype.card V : ℝ) - 1))) :
    (G.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) - 1 ∧ slack G = 0 := by
  have hnr : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hnp : (0 : ℝ) < Fintype.card V := by linarith
  have hn1 : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by linarith
  have hmr : (0 : ℝ) < G.edgeFinset.card := by exact_mod_cast edge_positive G hG hn
  have hs := slack_nonneg G hG hn
  have hid := defect_identity G hn (edge_positive G hG hn)
  rw [he, sub_self] at hid
  have hfirst : 0 ≤ (Fintype.card V : ℝ) * slack G / (4 * (G.edgeFinset.card : ℝ)^2) := by positivity
  have hsecond : 0 ≤ (Fintype.card V : ℝ)^2 *
      ((G.edgeFinset.card : ℝ) - Fintype.card V + 1)^2 /
      (4 * (G.edgeFinset.card : ℝ)^2 * ((Fintype.card V : ℝ) - 1)) := by positivity
  have hfirst0 : (Fintype.card V : ℝ) * slack G / (4 * (G.edgeFinset.card : ℝ)^2) = 0 := by linarith
  have hsecond0 : (Fintype.card V : ℝ)^2 *
      ((G.edgeFinset.card : ℝ) - Fintype.card V + 1)^2 /
      (4 * (G.edgeFinset.card : ℝ)^2 * ((Fintype.card V : ℝ) - 1)) = 0 := by linarith
  have hs0 : slack G = 0 := by
    have hprod := (div_eq_zero_iff.mp hfirst0).resolve_right (by positivity)
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hnp)
  have hsquare : ((G.edgeFinset.card : ℝ) - Fintype.card V + 1)^2 = 0 := by
    have hprod := (div_eq_zero_iff.mp hsecond0).resolve_right (by positivity)
    exact (mul_eq_zero.mp hprod).resolve_left (by positivity)
  have hm0 := (sq_eq_zero_iff).mp hsquare
  exact ⟨by linarith, hs0⟩

theorem equality_degree_endpoints (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hs : slack G = 0) (v : V) :
    (G.degree v : ℝ) = 1 ∨ (G.degree v : ℝ) = (Fintype.card V : ℝ) - 1 := by
  have hterm (w : V) : 0 ≤ ((G.degree w : ℝ) - 1) *
      ((Fintype.card V : ℝ) - 1 - G.degree w) := by
    have hp : (1 : ℝ) ≤ G.degree w := by exact_mod_cast degree_positive G hG hn w
    have hb : (G.degree w : ℝ) + 1 ≤ Fintype.card V := by
      exact_mod_cast (by have := G.degree_lt_card_verts w; omega : G.degree w + 1 ≤ Fintype.card V)
    exact mul_nonneg (by linarith) (by linarith)
  have hv := single_le_sum (fun w _ => hterm w) (mem_univ v)
  change _ ≤ slack G at hv
  rw [hs] at hv
  have hz : ((G.degree v : ℝ) - 1) * ((Fintype.card V : ℝ) - 1 - G.degree v) = 0 := le_antisymm hv (hterm v)
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem equality_isStar (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (he : dispersion G = ((Fintype.card V : ℝ) - 2)^2 /
      (4 * ((Fintype.card V : ℝ) - 1))) : IsStar G := by
  classical
  obtain ⟨hm, hs⟩ := equality_data G hG hn he
  have hends := equality_degree_endpoints G hG hn hs
  have hex : ∃ c : V, (G.degree c : ℝ) = (Fintype.card V : ℝ) - 1 := by
    by_cases hx : ∃ c : V, (G.degree c : ℝ) ≠ 1
    · obtain ⟨c, hc⟩ := hx
      exact ⟨c, (hends c).resolve_left hc⟩
    · push_neg at hx
      have hsum := degree_sum G
      simp only [hx, sum_const, card_univ, nsmul_eq_mul, mul_one] at hsum
      have hn2 : (Fintype.card V : ℝ) = 2 := by linarith
      have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      let c : V := Classical.choice inferInstance
      exact ⟨c, by rw [hx, hn2]; norm_num⟩
  obtain ⟨c, hc⟩ := hex
  have hcNat : G.degree c = Fintype.card V - 1 := by
    have hcast : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
      exact Nat.cast_sub (by omega)
    exact_mod_cast hc.trans hcast.symm
  have hmNat : G.edgeFinset.card = Fintype.card V - 1 := by
    have hcast : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
      exact Nat.cast_sub (by omega)
    exact_mod_cast hm.trans hcast.symm
  have hu : G.IsUniversal c := (G.degree_eq_card_sub_one c).mp hcNat
  have hinc : G.incidenceFinset c = G.edgeFinset := by
    apply eq_of_subset_of_card_le (G.incidenceFinset_subset c)
    simp only [card_incidenceFinset_eq_degree, hcNat, hmNat, le_refl]
  refine ⟨c, ?_⟩
  intro u v
  constructor
  · intro huv
    refine ⟨huv.ne, ?_⟩
    have hi : s(u, v) ∈ G.incidenceFinset c := by rw [hinc]; simpa using huv
    have hi' : s(u, v) ∈ G.incidenceSet c := by simpa only [mem_incidenceFinset] using hi
    have hcuv : c = u ∨ c = v := (G.mk'_mem_incidenceSet_iff.mp hi').2
    exact hcuv.imp Eq.symm Eq.symm
  · rintro ⟨hne, rfl | rfl⟩
    · exact hu hne
    · exact (hu hne.symm).symm

theorem star_data (hn : 2 ≤ Fintype.card V) (hs : IsStar G) :
    G.edgeFinset.card = Fintype.card V - 1 ∧ slack G = 0 := by
  classical
  obtain ⟨c, hc⟩ := hs
  have hu : G.IsUniversal c := by
    intro w hne
    exact (hc c w).mpr ⟨hne, Or.inl rfl⟩
  have hd : G.degree c = Fintype.card V - 1 := (G.degree_eq_card_sub_one c).mpr hu
  have hother (v : V) (hv : v ≠ c) : G.degree v = 1 := by
    have heq : G.neighborFinset v = {c} := by
      ext w
      simp only [mem_neighborFinset, mem_singleton]
      rw [hc v w]
      aesop
    rw [← card_neighborFinset_eq_degree, heq, card_singleton]
  have hsum : (∑ v : V, G.degree v) = 2 * (Fintype.card V - 1) := by
    have hrest : ∑ v ∈ univ.erase c, G.degree v = Fintype.card V - 1 := by
      calc
        (∑ v ∈ univ.erase c, G.degree v) = ∑ _v ∈ univ.erase c, 1 := by
          apply sum_congr rfl
          intro v hv
          exact hother v (ne_of_mem_erase hv)
        _ = Fintype.card V - 1 := by simp
    have ht := sum_erase_add (s := (univ : Finset V)) (f := G.degree) (a := c) (mem_univ c)
    rw [hrest, hd] at ht
    omega
  have hm : G.edgeFinset.card = Fintype.card V - 1 := by
    have := G.sum_degrees_eq_twice_card_edges
    omega
  refine ⟨hm, ?_⟩
  apply sum_eq_zero
  intro v _
  by_cases hv : v = c
  · subst v
    rw [hd, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
    ring
  · rw [hother v hv]
    norm_num

theorem conjecture2_equality (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    dispersion G = ((Fintype.card V : ℝ) - 2)^2 /
      (4 * ((Fintype.card V : ℝ) - 1)) ↔ IsStar G := by
  refine ⟨equality_isStar G hG hn, ?_⟩
  intro hs
  obtain ⟨hm, hslack⟩ := star_data G hn hs
  have hmreal : (G.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [hm, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
    norm_num
  have hz : (G.edgeFinset.card : ℝ) - Fintype.card V + 1 = 0 := by linarith
  have hid := defect_identity G hn (edge_positive G hG hn)
  simp only [hslack, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_div, add_zero] at hid
  linarith

end DegreeDispersionProof

#print axioms DegreeDispersionProof.conjecture2
#print axioms DegreeDispersionProof.equality_isStar
#print axioms DegreeDispersionProof.conjecture2_equality

