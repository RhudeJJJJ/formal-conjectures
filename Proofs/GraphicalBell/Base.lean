import Proofs.GraphicalBell.Partitions

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

lemma stable_card_le {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) : P.card ≤ S.card := by
  let part : Finpartition S :=
    { parts := P
      supIndep := supIndep_iff_pairwiseDisjoint.mpr (by
        intro B hB C hC hBC
        exact hP.2.1 B hB C hC hBC)
      sup_parts := by simpa only [sup_eq_biUnion] using hP.2.2
      bot_notMem := stable_empty_not_mem hP }
  exact part.card_parts_le_card


lemma stable_on_empty {G : SimpleGraph V} {P : Finset (Finset V)}
    (hP : StableOn G ∅ P) : P = ∅ := by
  ext B
  constructor
  · intro hb
    obtain ⟨x, hx⟩ := (hP.1 B hb).1
    exact (notMem_empty x (stable_subset hP hb hx)).elim
  · intro hb
    exact (notMem_empty B hb).elim

lemma empty_stable (G : SimpleGraph V) : StableOn G ∅ ∅ := by
  simp [StableOn]

lemma count_empty (G : SimpleGraph V) (k : ℕ) : count G ∅ k = if k = 0 then 1 else 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    let : Unique (Graded G ∅ 0) :=
      { default := ⟨⟨∅, empty_stable G⟩, rfl⟩
        uniq := fun P => Subtype.ext (Subtype.ext (stable_on_empty P.val.property)) }
    simp [count]
  · let : IsEmpty (Graded G ∅ k) :=
      ⟨fun P => hk (by rw [← P.property, stable_on_empty P.val.property]; rfl)⟩
    simp [count, hk]

lemma count_large {G : SimpleGraph V} {S : Finset V} {k : ℕ} (hk : S.card < k) :
    count G S k = 0 := by
  let : IsEmpty (Graded G S k) := ⟨fun P => by
    have h := stable_card_le P.val.property
    rw [P.property] at h
    omega⟩
  simp [count]

end GraphicalBellProof
