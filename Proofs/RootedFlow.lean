import FormalConjectures.WrittenOnTheWallII.GraphConjecture348

/-!
A finite rooted description of an actual simple tree, used to telescope local
integer potentials. No recursively substituted graph invariant is introduced.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Finset SimpleGraph

namespace WOWIIRootedFlow

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma exists_parent (hc : G.Connected) (r : V) :
    ∃ p : V → V, p r = r ∧ ∀ v, v ≠ r →
      G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r := by

  have hex : ∀ v, ∃ w, (v = r → w = r) ∧
      (v ≠ r → G.Adj v w ∧ G.dist w r + 1 = G.dist v r) := by
    intro v
    by_cases hv : v = r
    · exact ⟨r, fun _ => rfl, fun h => (h hv).elim⟩
    obtain ⟨walk, hlen⟩ := hc.exists_walk_length_eq_dist v r
    cases walk with
    | nil => exact (hv rfl).elim
    | @cons v w r hadj tail =>
      refine ⟨w, fun h => (hv h).elim, fun _ => ⟨hadj, ?_⟩⟩
      have htail := G.dist_le tail
      have htri := hadj.reachable.dist_triangle_left r
      rw [G.dist_eq_one_iff_adj.mpr hadj] at htri
      simp only [Walk.length_cons] at hlen
      omega
  choose p hp using hex
  exact ⟨p, (hp r).1 rfl, fun v hv => (hp v).2 hv⟩

def children (p : V → V) (r v : V) : Finset V :=
  Finset.univ.filter fun w => w ≠ r ∧ p w = v

lemma parent_classification (hT : G.IsTree) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r) :
    ∀ v w, G.Adj v w ↔ (v ≠ r ∧ p v = w) ∨ (w ≠ r ∧ p w = v) := by

  let S := (Finset.univ : Finset V).erase r
  let E := S.image fun v => s(v, p v)
  have hinj : Set.InjOn (fun v => s(v, p v)) (S : Set V) := by
    intro v hv w hw he
    rcases Sym2.eq_iff.mp he with he | he
    · exact he.1
    · have hvp := (hp v (Finset.mem_erase.mp hv).1).2
      have hwp := (hp w (Finset.mem_erase.mp hw).1).2
      rw [he.2] at hvp
      rw [← he.1] at hwp
      omega
  have hcardE : E.card = S.card := Finset.card_image_of_injOn hinj
  have hsub : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    simpa using (hp v (Finset.mem_erase.mp hv).1).1
  have hcardS : S.card + 1 = Fintype.card V := by
    simpa [S] using Finset.card_erase_add_one (Finset.mem_univ r)
  have ht := hT.card_edgeFinset
  have hEq : E = G.edgeFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro v w
  constructor
  · intro hadj
    have he : s(v, w) ∈ E := by rw [hEq]; simpa using hadj
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp he
    rcases Sym2.eq_iff.mp heq with heq | heq
    · obtain ⟨hfirst, hsecond⟩ := heq
      subst v
      exact Or.inl ⟨(Finset.mem_erase.mp hu).1, hsecond⟩
    · obtain ⟨hfirst, hsecond⟩ := heq
      subst w
      exact Or.inr ⟨(Finset.mem_erase.mp hu).1, hsecond⟩
  · rintro (⟨hv, rfl⟩ | ⟨hw, rfl⟩)
    · exact (hp v hv).1
    · exact (hp w hw).1.symm

lemma parent_not_child (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r)
    (v : V) (hv : v ≠ r) : p v ∉ children p r v := by
  intro hm
  obtain ⟨hpne, hpp⟩ := (Finset.mem_filter.mp hm).2
  have h1 := (hp v hv).2
  have h2 := (hp (p v) hpne).2
  rw [hpp] at h2
  omega

lemma degree_children (hT : G.IsTree) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r)
    (v : V) (hv : v ≠ r) : G.degree v = (children p r v).card + 1 := by
  have hclass := parent_classification G hT r p hp
  have heq : G.neighborFinset v = insert (p v) (children p r v) := by
    ext w
    simp [children, hclass, hv, eq_comm]
  have hc := congrArg Finset.card heq
  simpa [parent_not_child G r p hp v hv] using hc

lemma root_degree_children (hT : G.IsTree) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r) :
    G.degree r = (children p r r).card := by
  have hclass := parent_classification G hT r p hp
  have heq : G.neighborFinset r = children p r r := by
    ext w
    simp [children, hclass]
  exact congrArg Finset.card heq

lemma sum_children (r : V) (p : V → V) (f : V → ℤ) :
    (∑ v : V, ∑ w ∈ children p r v, f w) = ∑ w ∈ Finset.univ.erase r, f w := by

  have herase : (Finset.univ : Finset V).erase r =
      Finset.univ.filter fun w => w ≠ r := by
    ext w
    simp
  simp only [children, Finset.sum_filter]
  rw [Finset.sum_comm, herase, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : w = r
  · simp [h]
  · simp [h, eq_comm]

end WOWIIRootedFlow
