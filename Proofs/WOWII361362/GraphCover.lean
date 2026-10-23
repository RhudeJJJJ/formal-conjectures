import Mathlib.Combinatorics.SimpleGraph.Acyclic
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Lean.Elab.Tactic.Omega

open Finset SimpleGraph
namespace WOWIICover
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma forced_support {D : Finset V} (hD : G.IsTotalDominating (D : Set V))
    {s l : V} (hl : G.degree l = 1) (hsl : G.Adj s l) : s ∈ D := by
  obtain ⟨w, hw, hlw⟩ := hD l
  obtain ⟨a, ha, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hl
  have hw' := huniq w hlw
  have hs' := huniq s hsl.symm
  have : w=s := hw'.trans hs'.symm
  simpa only [Finset.mem_coe, this] using hw

lemma independent_component_representatives (S : Finset V) :
    ∃ R : Finset V, R ⊆ S ∧
      R.card = Nat.card (G.induce (S : Set V)).ConnectedComponent ∧
      ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b := by
  classical
  let H := G.induce (S : Set V)
  let _ := Fintype.ofFinite H.ConnectedComponent
  let r : H.ConnectedComponent → V := fun C => C.out.val
  have hm : ∀ C : H.ConnectedComponent, H.connectedComponentMk C.out = C :=
    fun C => C.out_eq
  have hinj : Function.Injective r := by
    intro C E he
    have hv : C.out = E.out := Subtype.ext he
    rw [← hm C, ← hm E, hv]
  let R : Finset V := univ.image r
  refine ⟨R, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨C, _, rfl⟩ := mem_image.mp hv
    exact C.out.property
  · rw [show R.card = Fintype.card H.ConnectedComponent by
          simp only [R, card_image_of_injective _ hinj, card_univ]]
    exact (Nat.card_eq_fintype_card).symm
  · intro a ha b hb hab
    obtain ⟨C, _, rfl⟩ := mem_image.mp ha
    obtain ⟨E, _, rfl⟩ := mem_image.mp hb
    have hEq : C=E := by
      rw [← hm C, ← hm E]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj
        (show H.Adj C.out E.out from hab)
    subst E
    exact hab.ne rfl

lemma distance_two_cover {D S : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hSD : S ⊆ D) :
    ∃ F : Finset V,
      F.card + Nat.card (G.induce (S : Set V)).ConnectedComponent = D.card ∧
      ∀ v, ∃ f ∈ F, G.dist v f ≤ 2 := by
  classical
  obtain ⟨R, hRS, hcard, hR⟩ := independent_component_representatives G S
  have hRD : R ⊆ D := hRS.trans hSD
  refine ⟨D \ R, ?_, ?_⟩
  · rw [card_sdiff_of_subset hRD, ← hcard]
    exact Nat.sub_add_cancel (card_le_card hRD)
  · intro v
    obtain ⟨d, hd, hvd⟩ := hD v
    by_cases hdr : d ∈ R
    · obtain ⟨f, hf, hdf⟩ := hD d
      have hfr : f ∉ R := fun h => hR d hdr f h hdf
      refine ⟨f, mem_sdiff.mpr ⟨hf,hfr⟩, ?_⟩
      have ht := hvd.reachable.dist_triangle_left f
      rw [G.dist_eq_one_iff_adj.mpr hvd, G.dist_eq_one_iff_adj.mpr hdf] at ht
      exact ht
    · refine ⟨d, mem_sdiff.mpr ⟨hd,hdr⟩, ?_⟩
      rw [G.dist_eq_one_iff_adj.mpr hvd]
      omega
end WOWIICover
