import FormalConjectures.WrittenOnTheWallII.GraphConjecture365

/-! Kernel proof of WOWII 365 and its integer strengthening.
The counting argument follows Gebendorfer's manuscript linked in PR 7370.
OpenAI Codex assisted with formalization. -/

namespace WOWII365Proof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture365

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : SimpleGraph V) [DecidableRel T.Adj]

def innerEdges (S : Finset V) : Finset (Sym2 V) :=
  T.edgeFinset.filter fun e => e.toFinset ⊆ S

@[simp] lemma mem_innerEdges (S : Finset V) (u v : V) :
    s(u,v) ∈ innerEdges T S ↔ T.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp [innerEdges, Sym2.toFinset_mk, insert_subset_iff]

lemma forest_budget (hT : T.IsTree) (D I : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) (hID : I ⊆ D)
    (hI : T.IsIndepSet (I : Set V)) :
    I.card + (innerEdges T (univ \\ D)).card + 1 ≤ D.card := by
  classical
  choose f hfD hf using hD
  let X := univ \\ D
  let H := X ∪ I
  let E := H.image fun v => s(v, f v)
  have hX : ∀ v ∈ X, v ∉ D := by simp [X]
  have hInj : Set.InjOn (fun v => s(v, f v)) (H : Set V) := by
    intro u hu v hv he
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.1
    · have huD : u ∈ D := h.1 ▸ hfD v
      have hvD : v ∈ D := h.2 ▸ hfD u
      have huI : u ∈ I := (mem_union.mp hu).resolve_left (fun hx => hX u hx huD)
      have hvI : v ∈ I := (mem_union.mp hv).resolve_left (fun hx => hX v hx hvD)
      exact False.elim (hI huI hvI (hf u).ne (by simpa [h.2] using hf u))
  have hEcard : E.card = H.card := card_image_of_injOn hInj
  have hEH : E ⊆ T.edgeFinset := by
    intro e he
    obtain ⟨v, _, rfl⟩ := mem_image.mp he
    simpa using hf v
  have hdis : Disjoint E (innerEdges T X) := by
    apply disjoint_left.mpr
    intro e he heX
    obtain ⟨v, _, rfl⟩ := mem_image.mp he
    have hfv := (mem_innerEdges T X v (f v)).mp heX
    exact hX (f v) hfv.2.2 (hfD v)
  have hsub : E ∪ innerEdges T X ⊆ T.edgeFinset := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hEH he
    · exact (mem_filter.mp he).1
  have hbound := card_le_card hsub
  rw [card_union_of_disjoint hdis, hEcard] at hbound
  have hXI : Disjoint X I := disjoint_left.mpr fun v hx hi => hX v hx (hID hi)
  have hHcard : H.card = X.card + I.card := card_union_of_disjoint hXI
  have htotal : X.card + D.card = Fintype.card V := by
    dsimp [X]
    rw [card_sdiff_of_subset (subset_univ D), card_univ]
    exact Nat.sub_add_cancel (card_le_univ D)
  have htree := hT.card_edgeFinset
  dsimp [X] at hbound hHcard
  omega

#print axioms forest_budget
end WOWII365Proof

