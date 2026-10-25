import Proofs.WOWII376354.RootPacking

/-! Full certificates for the three explicitly closed-neighborhood WOWII 354 targets. -/

open Finset SimpleGraph
namespace WrittenOnTheWallII.GraphConjecture354
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : SimpleGraph V)

omit [DecidableEq V] in
lemma packing_card_le_total {P D : Finset V}
    (hP : (P : Set V).Pairwise fun u v => Disjoint (T.neighborSet u) (T.neighborSet v))
    (hD : T.IsTotalDominating (D : Set V)) : P.card ≤ D.card := by
  classical
  have hex : ∀ p : P, ∃ d : D, T.Adj p.val d.val := by
    intro p
    obtain ⟨d,hd,hpd⟩ := hD p.val
    exact ⟨⟨d,hd⟩,hpd⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro p q he
    by_contra hn
    have hne : p.val ≠ q.val := fun h => hn (Subtype.ext h)
    have hdis := hP p.property q.property hne
    have hbad := Set.disjoint_left.mp hdis (hf p)
    apply hbad
    have hpq := hf q
    rw [← he] at hpq
    exact hpq
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

lemma open_packing_le_total (hT : T.IsTree) (ho : 1 < Fintype.card V) :
    openPackingNumber T ≤ T.totalDominationNumber := by
  classical
  obtain ⟨D,hD,hcard⟩ := WOWIICover.minimum_total_set T hT.connected ho
  unfold openPackingNumber
  apply Finset.sup_le
  intro P hP
  rw [← hcard]
  exact packing_card_le_total T (mem_filter.mp hP).2 hD

theorem full_closed_neighborhood_bound [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 1 < Fintype.card V) (A : Finset V)
    (hA : ∀ v ∈ A, 2 ≤ T.degree v) :
    2 * componentsOn T (closedNeighbors T A) ≤ openPackingNumber T ∧
      openPackingNumber T ≤ T.totalDominationNumber := by
  classical
  obtain ⟨P,hcard,hP⟩ := WOWIIRootPacking.packing_two_per_component T hT A hA
  refine ⟨?_,open_packing_le_total T hT horder⟩
  rw [← hcard]
  unfold openPackingNumber
  apply Finset.le_sup
  exact mem_filter.mpr ⟨mem_powerset.mpr (subset_univ P),hP⟩

theorem full_degree_two_bound [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 1 < Fintype.card V) :
    2 * componentsOn T (closedNeighbors T (degreeTwo T)) ≤ T.totalDominationNumber := by
  have hA : ∀ v ∈ degreeTwo T, 2 ≤ T.degree v := by
    intro v hv
    exact le_of_eq ((mem_filter.mp hv).2.symm)
  have h := full_closed_neighborhood_bound T hT horder (degreeTwo T) hA
  exact h.1.trans h.2

theorem full_conjecture354_closed [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2 < Fintype.card V) :
    Nat.card T.center * componentsOn T (closedNeighbors T (degreeTwo T)) ≤
      T.totalDominationNumber := by
  exact (Nat.mul_le_mul_right _ (WOWIIGeometry.center_card_le_two T hT)).trans
    (full_degree_two_bound T hT (by omega))

end WrittenOnTheWallII.GraphConjecture354
