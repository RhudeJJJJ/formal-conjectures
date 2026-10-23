import FormalConjectures.WrittenOnTheWallII.GraphConjecture362
import Proofs.WOWII361362.GraphCover
import Proofs.WOWII361362.TreeGeometry
import Proofs.WOWII361362.SupportComponents

namespace WrittenOnTheWallII.GraphConjecture362
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma supports_forced (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : Finset V} (hD : G.IsTotalDominating (D : Set V)) : supports G ⊆ D := by
  intro s hs
  obtain ⟨l,hl,hsl⟩ := (mem_filter.mp hs).2
  exact WOWIICover.forced_support G hD hl hsl

theorem full_conjecture362_diameter (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (horder : 2 < Fintype.card V) :
    (G.diam : ℤ)+1 ≤ 5*((G.totalDominationNumber : ℤ) -
      (componentsOn G (supports G) : ℤ)) := by
  classical
  obtain ⟨D,hD,hcard⟩ := WOWIICover.minimum_total_set G hG (by omega)
  obtain ⟨F,hFcard,hcover⟩ := WOWIICover.distance_two_cover G hD (supports_forced G hD)
  have hdiam := WOWIICover.diameter_of_two_cover G hG F hcover
  change F.card + componentsOn G (supports G) = D.card at hFcard
  rw [hcard] at hFcard
  omega

theorem full_conjecture362 (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2 < Fintype.card V) :
    (componentsOn T (supports T ∪ leaves T) : ℚ) +
      (1+(T.radius.toNat : ℚ))/3 ≤ T.totalDominationNumber := by
  classical
  let _ := hT.connected.nonempty
  obtain ⟨D,hD,hcard⟩ := WOWIICover.minimum_total_set T hT.connected (by omega)
  obtain ⟨F,hFcard,hcover⟩ := WOWIICover.distance_two_cover T hD (supports_forced T hD)
  have hdiam := WOWIICover.diameter_of_two_cover T hT.connected F hcover
  have hradius := WOWIIGeometry.radius_midpoint_bound T hT
  have hpos : 0 < F.card := by
    obtain ⟨f,hf,_⟩ := hcover (Classical.ofNonempty : V)
    exact card_pos.mpr ⟨f,hf⟩
  change F.card + componentsOn T (supports T) = D.card at hFcard
  rw [hcard] at hFcard
  have hn : 3*componentsOn T (supports T)+T.radius.toNat+1 ≤
      3*T.totalDominationNumber := by omega
  have hq : (3 : ℚ)*componentsOn T (supports T)+(T.radius.toNat : ℚ)+1 ≤
      3*(T.totalDominationNumber : ℚ) := by exact_mod_cast hn
  rw [SupportComponentsProof.support_components_eq T hT.connected horder]
  linarith

#print axioms full_conjecture362_diameter
#print axioms full_conjecture362
end WrittenOnTheWallII.GraphConjecture362
