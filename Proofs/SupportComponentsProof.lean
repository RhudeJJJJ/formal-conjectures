import FormalConjectures.WrittenOnTheWallII.GraphConjecture362

/-! Adding leaves to the induced support graph preserves its components.
This proves the identity in Gebendorfer's issue7237 manuscript, and in fact
does not require connectedness or an order restriction.
OpenAI Codex assisted with formalization. -/

namespace SupportComponentsProof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture362

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]

theorem components_support_union_leaves :
    componentsOn G (supports G ∪ leaves G) = componentsOn G (supports G) := by
  classical
  let A := {v : V // v ∈ supports G}
  let B := {v : V // v ∈ supports G ∪ leaves G}
  let GA := G.induce (supports G : Set V)
  let GB := G.induce ((supports G ∪ leaves G : Finset V) : Set V)
  let inclusion : GA →g GB :=
    { toFun := fun v => ⟨v.val, mem_union_left _ v.property⟩
      map_rel' := fun h => h }
  have hex : ∀ v : B, ∃ s : A,
      (v.val ∈ supports G → s.val = v.val) ∧
      (v.val ∉ supports G → ∀ w, G.Adj v.val w → w = s.val) ∧
      (s.val = v.val ∨ G.Adj v.val s.val) := by
    intro v
    by_cases hv : v.val ∈ supports G
    · exact ⟨⟨v.val, hv⟩, fun _ => rfl, fun hn => (hn hv).elim, Or.inl rfl⟩
    have hl : v.val ∈ leaves G := (mem_union.mp v.property).resolve_left hv
    have hd : G.degree v.val = 1 := (mem_filter.mp hl).2
    obtain ⟨s, hs, huniq⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hd
    have hS : s ∈ supports G := by
      simp only [supports, mem_filter, mem_univ, true_and]
      exact ⟨v.val, hd, hs.symm⟩
    exact ⟨⟨s, hS⟩, fun h => (hv h).elim, fun _ w hw => huniq w hw, Or.inr hs⟩
  choose r hr using hex
  have hadj : ∀ u v : B, GB.Adj u v →
      GA.connectedComponentMk (r u) = GA.connectedComponentMk (r v) := by
    intro u v huv
    by_cases hu : u.val ∈ supports G
    · by_cases hv : v.val ∈ supports G
      · apply ConnectedComponent.connectedComponentMk_eq_of_adj
        change G.Adj (r u).val (r v).val
        rw [(hr u).1 hu, (hr v).1 hv]
        exact huv
      · have he : u.val = (r v).val := (hr v).2.1 hv u.val huv.symm
        have hrv : r u = r v := Subtype.ext (((hr u).1 hu).trans he)
        rw [hrv]
    · have he : v.val = (r u).val := (hr u).2.1 hu v.val huv
      have hv : v.val ∈ supports G := he ▸ (r u).property
      have hrv : r v = r u := Subtype.ext (((hr v).1 hv).trans he)
      rw [hrv]
  have hwalk : ∀ {u v : B}, GB.Walk u v →
      GA.connectedComponentMk (r u) = GA.connectedComponentMk (r v) := by
    intro u v p
    induction p with
    | nil => rfl
    | @cons a b c hab p ih => exact (hadj a b hab).trans ih
  let retreat : GB.ConnectedComponent → GA.ConnectedComponent :=
    Quot.lift (fun v => GA.connectedComponentMk (r v))
      (fun _ _ h => h.elim hwalk)
  have hleft : ∀ c : GA.ConnectedComponent, retreat (c.map inclusion) = c := by
    intro c
    induction c using ConnectedComponent.ind with
    | h v =>
      change GA.connectedComponentMk (r (inclusion v)) = GA.connectedComponentMk v
      congr 1
      exact Subtype.ext ((hr (inclusion v)).1 v.property)
  have hright : ∀ c : GB.ConnectedComponent, (retreat c).map inclusion = c := by
    intro c
    induction c using ConnectedComponent.ind with
    | h v =>
      change GB.connectedComponentMk (inclusion (r v)) = GB.connectedComponentMk v
      rcases (hr v).2.2 with he | he
      · congr 1
        exact Subtype.ext he
      · apply ConnectedComponent.sound
        exact (show GB.Adj v (inclusion (r v)) from he).reachable.symm
  let e : GA.ConnectedComponent ≃ GB.ConnectedComponent :=
    { toFun := ConnectedComponent.map inclusion
      invFun := retreat
      left_inv := hleft
      right_inv := hright }
  exact (Nat.card_congr e).symm

theorem support_components_eq (_hG : G.Connected) (_horder : 2 < Fintype.card V) :
    componentsOn G (supports G ∪ leaves G) = componentsOn G (supports G) := by
  exact components_support_union_leaves G

end SupportComponentsProof

#print axioms SupportComponentsProof.components_support_union_leaves
#print axioms SupportComponentsProof.support_components_eq
