import Proofs.TDAGraphBasics
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! A tree admits a vertex two-coloring with both colors in every non-leaf neighborhood. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem fin_two_eq_of_ne {a b c : Fin 2} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

omit [DecidableEq V] in
/-- A non-root vertex with at least two neighbors has a parent and a child. -/
theorem tree_parent_child (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (r u : V) (hne : u ≠ r) (hdeg : 2 ≤ G.degree u) :
    ∃ p q : V, G.Adj u p ∧ G.Adj u q ∧
      G.dist r p + 1 = G.dist r u ∧ G.dist r q = G.dist r u + 1 := by
  classical
  obtain ⟨P, hP, hPlen⟩ := hG.connected.exists_path_of_dist u r
  have hPn : ¬ P.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  let p := P.snd
  have hup : G.Adj u p := P.adj_snd hPn
  have htail := G.dist_le P.tail
  have hlength := P.length_tail_add_one hPn
  have hdistp := hG.dist_eq_dist_add_one_of_adj r hup
  change G.dist p r ≤ P.tail.length at htail
  rw [G.dist_comm] at htail
  rw [G.dist_comm] at hPlen
  have hpdist : G.dist r p + 1 = G.dist r u := by
    change G.dist r p ≤ P.tail.length at htail
    omega
  have hex : ∃ q ∈ G.neighborFinset u, q ≠ p := by
    by_contra hbad
    have hsub : G.neighborFinset u ⊆ {p} := by
      intro q hq
      have hqp : q = p := by by_contra hne'; exact hbad ⟨q, hq, hne'⟩
      exact mem_singleton.mpr hqp
    have hc := card_le_card hsub
    change G.degree u ≤ ({p} : Finset V).card at hc
    simp only [card_singleton] at hc
    omega
  obtain ⟨q, hqN, hqp⟩ := hex
  have huq : G.Adj u q := (mem_neighborFinset _ _ _).mp hqN
  have hqnot : q ∉ P.support := by
    intro hqP
    exact hqp (hG.isAcyclic.eq_snd_of_adj_start hP huq hqP)
  have hcons : (P.cons huq.symm).IsPath := hP.cons hqnot
  obtain ⟨Q, hQ, hQlen⟩ := hG.connected.exists_path_of_dist q r
  have heq : P.cons huq.symm = Q := Subtype.mk.inj
    ((hG.isAcyclic.subsingleton_path q r).elim ⟨_, hcons⟩ ⟨Q, hQ⟩)
  have hlen := congrArg SimpleGraph.Walk.length heq
  simp only [SimpleGraph.Walk.length_cons] at hlen
  rw [G.dist_comm q r] at hQlen
  exact ⟨p, q, hup, huq, hpdist, by omega⟩

omit [DecidableEq V] in
/-- Both colors occur at every vertex of degree at least two. -/
theorem tree_neighborhood_two_coloring (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (hn : 2 ≤ Fintype.card V) :
    ∃ color : V → Fin 2, ∀ u, 2 ≤ G.degree u →
      ∀ i : Fin 2, ∃ v, G.Adj u v ∧ color v = i := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a⟩ := hG.connected.nonempty
  obtain ⟨b, hab⟩ := (G.degree_pos_iff_exists_adj a).mp
    (hG.connected.preconnected.degree_pos_of_nontrivial a)
  let c := hG.coloringTwo
  have hcab : c a ≠ c b := c.valid hab
  let root := fun v => if c v = c a then a else b
  have hroot : ∀ v, c (root v) = c v := by
    intro v
    dsimp [root]
    split_ifs with h
    · exact h.symm
    · exact (fin_two_eq_of_ne (Ne.symm h) hcab).symm
  let color := fun v => (⟨G.dist (root v) v / 2 % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2)
  refine ⟨color, ?_⟩
  intro u hdeg i
  obtain ⟨x, hux⟩ := (G.degree_pos_iff_exists_adj u).mp (by omega)
  let r := root x
  have hur : u ≠ r := by
    intro hur
    have hcu := c.valid hux
    have hcx := hroot x
    change c r = c x at hcx
    rw [← hur] at hcx
    exact hcu hcx
  have hsame : ∀ v, G.Adj u v → root v = r := by
    intro v huv
    have hc : c v = c x := fin_two_eq_of_ne (c.valid huv) (c.valid hux)
    dsimp [root, r]
    rw [hc]
  obtain ⟨p, q, hup, huq, hpd, hqd⟩ := tree_parent_child G hG r u hur hdeg
  have hneq : color p ≠ color q := by
    intro heq
    have hv := congrArg Fin.val heq
    change (G.dist (root p) p / 2 % 2) = (G.dist (root q) q / 2 % 2) at hv
    rw [hsame p hup, hsame q huq] at hv
    omega
  by_cases hpi : color p = i
  · exact ⟨p, hup, hpi⟩
  · exact ⟨q, huq, (fin_two_eq_of_ne hpi hneq).symm⟩

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.tree_neighborhood_two_coloring
