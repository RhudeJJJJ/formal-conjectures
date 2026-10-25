import Proofs.GraphicalBell.Recovery

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

abbrev Choices (G : SimpleGraph V) (P : Finset (Finset V)) (v : V) :=
  {B : Finset V // B ∈ P ∧ ∀ w ∈ B, ¬ G.Adj v w}

instance finiteChoices (G : SimpleGraph V) (P : Finset (Finset V)) (v : V) :
    Finite (Choices G P v) := by
  let f : Choices G P v → P := fun B => ⟨B.val, B.property.1⟩
  apply Finite.of_injective f
  intro B C h
  apply Subtype.ext
  exact congrArg (fun D : P => D.val) h

noncomputable instance choicesFintype (G : SimpleGraph V) (P : Finset (Finset V)) (v : V) :
    Fintype (Choices G P v) := Fintype.ofFinite _

abbrev InsertionData (G : SimpleGraph V) (S : Finset V) (v : V) (k : ℕ) :=
  Graded G S k ⊕ (Σ P : Graded G S (k + 1), Choices G P.val.val v)

noncomputable def insertData {G : SimpleGraph V} {S : Finset V} {v : V} (hv : v ∉ S)
    {k : ℕ} : InsertionData G S v k → Graded G (insert v S) (k + 1)
  | Sum.inl P => ⟨⟨extendVertex v P.val.val ∅,
      extend_stable P.val.property hv (Or.inl rfl) (by simp)⟩,
      by simp [extend_card P.val.property hv (Or.inl rfl), P.property]⟩
  | Sum.inr ⟨P, B⟩ => ⟨⟨extendVertex v P.val.val B.val,
      extend_stable P.val.property hv (Or.inr B.property.1) B.property.2⟩,
      by simpa [extend_card P.val.property hv (Or.inr B.property.1),
        ne_of_mem_of_not_mem B.property.1 (stable_empty_not_mem P.val.property)] using P.property⟩

lemma insertData_injective {G : SimpleGraph V} {S : Finset V} {v : V} (hv : v ∉ S)
    (k : ℕ) : Function.Injective (insertData (G := G) hv (k := k)) := by
  intro a b he
  have he' := congrArg (fun Q : Graded G (insert v S) (k + 1) => Q.val.val) he
  cases a with
  | inl P =>
      cases b with
      | inl R =>
          obtain ⟨hPR, _⟩ := extend_injective P.val.property R.val.property hv
            (Or.inl rfl) (Or.inl rfl) (by simp) he'
          have h : P = R := Subtype.ext (Subtype.ext hPR)
          exact congrArg Sum.inl h
      | inr pair =>
          obtain ⟨R, B⟩ := pair
          obtain ⟨_, hB⟩ := extend_injective P.val.property R.val.property hv
            (Or.inl rfl) (Or.inr B.property.1) (by simp) he'
          exact (stable_empty_not_mem R.val.property (hB.symm ▸ B.property.1)).elim
  | inr pair =>
      obtain ⟨P, B⟩ := pair
      cases b with
      | inl R =>
          obtain ⟨_, hB⟩ := extend_injective P.val.property R.val.property hv
            (Or.inr B.property.1) (Or.inl rfl) B.property.2 he'
          exact (stable_empty_not_mem P.val.property (hB ▸ B.property.1)).elim
      | inr pair =>
          obtain ⟨R, C⟩ := pair
          obtain ⟨hPR, hBC⟩ := extend_injective P.val.property R.val.property hv
            (Or.inr B.property.1) (Or.inr C.property.1) B.property.2 he'
          have h : P = R := Subtype.ext (Subtype.ext hPR)
          cases h
          have hB : B = C := Subtype.ext hBC
          cases hB
          rfl

lemma insertData_surjective {G : SimpleGraph V} {S : Finset V} {v : V} (hv : v ∉ S)
    (k : ℕ) : Function.Surjective (insertData (G := G) hv (k := k)) := by
  intro Q
  have hQ := Q.val.property
  have hvQ : v ∈ Q.val.val.biUnion id := by rw [hQ.2.2]; exact mem_insert_self _ _
  obtain ⟨U, hU, hvU⟩ := mem_biUnion.mp hvQ
  let P : Parts G S := ⟨removeVertex v Q.val.val, by
    simpa [erase_insert hv] using remove_stable hQ v⟩
  have hb := removed_block_eligible hQ hU hvU
  have hr := reconstruct hQ hU hvU
  have hcard := extend_card P.property hv hb.1
  change (extendVertex v P.val (U.erase v)).card = _ at hcard
  rw [hr, Q.property] at hcard
  by_cases hempty : U.erase v = ∅
  · have hp : P.val.card = k := by simp [hempty] at hcard; omega
    refine ⟨Sum.inl ⟨P, hp⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change extendVertex v P.val ∅ = Q.val.val
    simpa [hempty] using hr
  · have hp : P.val.card = k + 1 := by simp only [if_neg hempty] at hcard; omega
    refine ⟨Sum.inr ⟨⟨P, hp⟩, ⟨U.erase v, hb.1.resolve_left hempty, hb.2⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hr

open scoped Classical in
lemma count_insert {G : SimpleGraph V} {S : Finset V} {v : V}
    (hv : v ∉ S) (k : ℕ) :
    count G (insert v S) (k + 1) = count G S k +
      ∑ P : Graded G S (k + 1), Nat.card (Choices G P.val.val v) := by
  classical
  let : Fintype (Σ P : Graded G S (k + 1), Choices G P.val.val v) := inferInstance
  let e : InsertionData G S v k ≃ Graded G (insert v S) (k + 1) :=
    Equiv.ofBijective (insertData hv) ⟨insertData_injective hv k, insertData_surjective hv k⟩
  rw [count, ← Nat.card_congr e, Nat.card_sum, Nat.card_sigma]

end GraphicalBellProof
