import Proofs.GraphicalBell.Deletion

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

lemma choices_exact_of_clique {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) (v : V)
    (hs : ∀ x ∈ S, G.Adj v x → ∀ y ∈ S, G.Adj v y → x ≠ y → G.Adj x y) :
    Nat.card (Choices G P v) = P.card - degreeOn G S v := by
  classical
  let free : Finset (Finset V) := P.filter (fun B => ∀ w ∈ B, ¬ G.Adj v w)
  let bad : Finset (Finset V) := P.filter (fun B => ∃ w ∈ B, G.Adj v w)
  let N : Finset V := S.filter (G.Adj v)
  have choose_block : ∀ x : N, ∃ B ∈ P, x.val ∈ B := by
    intro x
    apply mem_biUnion.mp
    change x.val ∈ P.biUnion id
    rw [hP.2.2]
    exact (mem_filter.mp x.property).1
  let f : N → bad := fun x =>
    let B := Classical.choose (choose_block x)
    have hB := Classical.choose_spec (choose_block x)
    ⟨B, mem_filter.mpr ⟨hB.1, x.val, hB.2, (mem_filter.mp x.property).2⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    by_contra hxy
    have hx := Classical.choose_spec (choose_block x)
    have hy := Classical.choose_spec (choose_block y)
    have he' := congrArg (fun B : bad => B.val) he
    change Classical.choose (choose_block x) = Classical.choose (choose_block y) at he'
    have hAdj := hs x.val (mem_filter.mp x.property).1 (mem_filter.mp x.property).2
      y.val (mem_filter.mp y.property).1 (mem_filter.mp y.property).2 hxy
    exact (hP.1 _ hx.1).2 hx.2 (he'.symm ▸ hy.2) hxy hAdj
  have hsurj : Function.Surjective f := by
    intro B
    obtain ⟨x, hx, hadj⟩ := (mem_filter.mp B.property).2
    let xN : N := ⟨x, mem_filter.mpr ⟨stable_subset hP (mem_filter.mp B.property).1 hx, hadj⟩⟩
    refine ⟨xN, Subtype.ext ?_⟩
    have hchosen := Classical.choose_spec (choose_block xN)
    exact stable_unique hP hchosen.1 (mem_filter.mp B.property).1 hchosen.2 hx
  have hbad : N.card = bad.card := by
    have h := Nat.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)
    simpa using h
  have hchoices : Nat.card (Choices G P v) = free.card := by
    have e : Choices G P v ≃ free :=
      
        { toFun := fun B => ⟨B.val, mem_filter.mpr B.property⟩
          invFun := fun B => ⟨B.val, mem_filter.mp B.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    simp
  have hsum : free.card + bad.card = P.card := by
    have h := card_filter_add_card_filter_not (s := P) (fun B => ∀ w ∈ B, ¬ G.Adj v w)
    simpa only [free, bad, not_forall, not_imp, not_not] using h
  rw [hchoices]
  change free.card = P.card - N.card
  omega

open scoped Classical in
lemma simplicial_recurrence {G : SimpleGraph V} {S : Finset V} {v : V} (hv : v ∉ S)
    (hs : ∀ x ∈ S, G.Adj v x → ∀ y ∈ S, G.Adj v y → x ≠ y → G.Adj x y) (k : ℕ) :
    count G (insert v S) (k + 1) = count G S k +
      (k + 1 - degreeOn G S v) * count G S (k + 1) := by
  rw [count_insert hv k]
  congr 1
  have h : ∀ P : Graded G S (k + 1), Nat.card (Choices G P.val.val v) =
      k + 1 - degreeOn G S v := by
    intro P
    rw [choices_exact_of_clique P.val.property v hs, P.property]
  simp_rw [h]
  simp [count, Nat.card_eq_fintype_card, mul_comm]

end GraphicalBellProof
