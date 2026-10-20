/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFourVertexSpectrum

/-!
# Complete RG energy coverage through order four

A four-vertex nonpath tree is a star. Exact path/star energies therefore
discharge SmallOrders 5, including the equality characterization. Uniform
strict fusion above five is still an explicit unproved global input.
-/

namespace Gebendorfer.RadenkovicGutman.OrderFour

open SimpleGraph TreeTerminal GlobalAssembly FourVertexSpectrum
open scoped Classical
noncomputable section

def starIso (r : Fin 4) : starGraph r ≃g starFour := by
  let e := Equiv.swap r (0 : Fin 4)
  have he : e r = 0 := by simp [e]
  have f : starGraph r ≃g starGraph (e r) :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        simp only [starGraph_adj, ne_eq, e.injective.eq_iff] }
  simpa only [he, starFour] using f

theorem nonpath_iso_starFour (T : SimpleGraph (Fin 4)) (hT : T.IsTree)
    (hp : ¬Nonempty (T ≃g pathGraph 4)) : Nonempty (T ≃g starFour) := by
  have hd : ¬∀ v, T.degree v ≤ 2 := by
    intro h
    apply hp
    have hi := tree_path_iso_of_degree_le_two T hT h
    rw [Fintype.card_fin] at hi
    exact hi
  push Not at hd
  obtain ⟨r, hr⟩ := hd
  have hlt := T.degree_lt_card_verts r
  rw [Fintype.card_fin] at hlt
  have he : T.degree r = 3 := by omega
  have hu : T.IsUniversal r := (T.degree_eq_card_sub_one r).mp (by simpa using he)
  have hle : starGraph r ≤ T := by
    intro a b hab
    obtain ⟨hne, h | h⟩ := starGraph_adj.mp hab
    · subst a
      exact hu hne
    · subst b
      exact (hu hne.symm).symm
  have heq : starGraph r = T := le_antisymm hle
    ((isTree_iff_minimal_connected.mp hT).2 (connected_starGraph r) hle)
  rw [← heq]
  exact ⟨starIso r⟩

theorem conclusion_four (T : SimpleGraph (Fin 4)) (hT : T.IsTree) : Conclusion T := by
  by_cases hp : Nonempty (T ≃g pathGraph 4)
  · obtain ⟨f⟩ := hp
    exact conclusion_of_iso T f
  · obtain ⟨f⟩ := nonpath_iso_starFour T hT hp
    have he := energy_iso f
    have hs : laplacianEnergy (pathGraph 4) < laplacianEnergy T := by
      rw [he]
      exact pathFour_energy_lt_starFour
    refine ⟨hs.le, ?_⟩
    constructor
    · intro h
      exact ((ne_of_gt hs) h).elim
    · intro h
      exact (hp h).elim

theorem smallOrders_five : GlobalAssembly.SmallOrders 5 := by
  intro n hn hn5 T hT
  by_cases hn4 : n < 4
  · exact SmallOrders.smallOrders_four n hn hn4 T hT
  · have he : n = 4 := by omega
    subst n
    exact conclusion_four T hT

theorem smallOrders_iff_from_five (N : ℕ) :
    GlobalAssembly.SmallOrders N ↔
      ∀ n, 5 ≤ n → n < N → ∀ T : SimpleGraph (Fin n), T.IsTree → Conclusion T := by
  constructor
  · intro h n hn hnN T hT
    exact h n (by omega) hnN T hT
  · intro h n hn hnN T hT
    by_cases hn5 : n < 5
    · exact smallOrders_five n hn hn5 T hT
    · exact h n (by omega) hnN T hT

theorem universal_conclusion_of_strictFusion_five (hF : StrictFusionAbove 5)
    (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) : Conclusion T :=
  SourcePresentation.universal_conclusion_of_inputs 5 smallOrders_five hF n hn T hT

theorem path_minimum_of_strictFusion_five (hF : StrictFusionAbove 5)
    (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    laplacianEnergy (pathGraph n) ≤ laplacianEnergy T :=
  (universal_conclusion_of_strictFusion_five hF n hn T hT).1

theorem path_equality_of_strictFusion_five (hF : StrictFusionAbove 5)
    (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    laplacianEnergy T = laplacianEnergy (pathGraph n) ↔ Nonempty (T ≃g pathGraph n) :=
  (universal_conclusion_of_strictFusion_five hF n hn T hT).2

#check @smallOrders_five
#check @universal_conclusion_of_strictFusion_five
#check @path_minimum_of_strictFusion_five
#check @path_equality_of_strictFusion_five

#print axioms starIso
#print axioms nonpath_iso_starFour
#print axioms conclusion_four
#print axioms smallOrders_five
#print axioms smallOrders_iff_from_five
#print axioms universal_conclusion_of_strictFusion_five
#print axioms path_minimum_of_strictFusion_five
#print axioms path_equality_of_strictFusion_five

end
end Gebendorfer.RadenkovicGutman.OrderFour
