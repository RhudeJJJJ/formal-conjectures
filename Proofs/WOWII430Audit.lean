import Proofs.WOWII430Proof

/-! Construction and definition audit for the explicit upper/M and upper/center
readings of WOWII 430c. The cyclic construction has 21 clique points and four
copies of each translate of {0,1,4,14,16} modulo 21. -/
namespace WOWII430Audit
open WOWII430Proof SimpleGraph Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def incidence (p o : ℕ) : Prop := p < 21 ∧ 21 ≤ o ∧
  (p = ((o-21)/4)%21 ∨ p = ((o-21)/4+1)%21 ∨ p = ((o-21)/4+4)%21 ∨
    p = ((o-21)/4+14)%21 ∨ p = ((o-21)/4+16)%21)
def constructedAdj (u v : Fin 105) : Prop := u ≠ v ∧
  ((u.val < 21 ∧ v.val < 21) ∨ incidence u.val v.val ∨ incidence v.val u.val)
lemma construction_matches : ∀ u v : Fin 105, witness.Adj u v ↔ constructedAdj u v := by
  unfold constructedAdj incidence
  decide

lemma center_matches {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (WOWII430Proof.center G : Set V) = G.center := by
  classical
  ext v
  simp [WOWII430Proof.center, SimpleGraph.center]

lemma all_induced_bounds (S : Finset (Fin 105)) : boundOn witness S ≤ 60 := by
  rw [boundOn, square_residue_eq, mul_one]
  have hl := max_local_bound
  have hd := induced_degree_bound S
  omega

lemma singleton_not_dominating : ¬ witness.IsDominating ({0} : Set (Fin 105)) := by
  simp only [SimpleGraph.IsDominating, Set.mem_singleton_iff]
  decide

#print axioms construction_matches
#print axioms center_matches
#print axioms all_induced_bounds
end WOWII430Audit
