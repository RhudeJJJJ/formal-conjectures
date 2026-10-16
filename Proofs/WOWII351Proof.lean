import FormalConjectures.WrittenOnTheWallII.GraphConjecture351

/-! A complete disproof of the literal WOWII351 statement, using the k=2 tree
from the manuscript. Component injections and a total dominating set suffice;
neither exact optimality nor the infinite family is asserted here. -/

namespace WOWII351Proof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture351
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def parent : Fin 44 → Fin 44 := ![0,0,1,1,0,4,4,6,7,7,9,9,11,12,11,14,8,16,16,18,8,20,20,22,0,24,24,26,27,27,29,29,31,32,31,34,28,36,36,38,28,40,40,42]

def witness : SimpleGraph (Fin 44) where
  Adj v w := v ≠ w ∧ (parent v = w ∨ parent w = v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel witness.Adj :=
  inferInstanceAs (DecidableRel fun v w => v ≠ w ∧ (parent v = w ∨ parent w = v))

theorem parent_lt : ∀ v : Fin 44, v ≠ 0 → (parent v).val < v.val := by decide

theorem reaches_zero (v : Fin 44) : witness.Reachable v 0 := by
  have aux : ∀ n : ℕ, ∀ v : Fin 44, v.val = n → witness.Reachable v 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases hz : w = 0
      · subst w
        exact .refl 0
      have hp := parent_lt w hz
      have ha : witness.Adj w (parent w) := by
        refine ⟨?_, Or.inl rfl⟩
        intro he
        have hv := congrArg Fin.val he
        omega
      exact ha.reachable.trans (ih (parent w).val (by omega) (parent w) rfl)
  exact aux v.val v rfl

theorem witness_connected : witness.Connected :=
  ⟨fun u v => (reaches_zero u).trans (reaches_zero v).symm⟩

theorem witness_tree : witness.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨witness_connected, ?_⟩
  have he : witness.edgeFinset.card = 43 := by decide
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, he,
    Nat.card_eq_fintype_card]
  decide

def selected : Finset (Fin 44) := {0,1,4,9,11,12,14,16,18,20,22,24,29,31,32,34,36,38,40,42}
theorem selected_total : witness.IsTotalDominating (selected : Set (Fin 44)) := by
  change ∀ v : Fin 44, ∃ w ∈ selected, witness.Adj v w
  decide

theorem total_bound : witness.totalDominationNumber ≤ 20 :=
  Nat.sInf_le ⟨selected, selected_total, by decide⟩

theorem labeled_components_lower {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (n : ℕ) (label : W → Fin n) (rep : Fin n → W)
    (hrep : ∀ i, label (rep i) = i)
    (hadj : ∀ u v, H.Adj u v → label u = label v) :
    n ≤ Nat.card H.ConnectedComponent := by
  classical
  have hwalk : ∀ {u v : W}, H.Walk u v → label u = label v := by
    intro u v p
    induction p with
    | nil => rfl
    | @cons a b c hab p ih => exact (hadj a b hab).trans ih
  let f : Fin n → H.ConnectedComponent := fun i => H.connectedComponentMk (rep i)
  have hf : Function.Injective f := by
    intro i j hij
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hij
    simpa only [hrep] using hwalk p
  have hc := Nat.card_le_card_of_injective (f := f) hf
  simpa using hc

def setA : Finset (Fin 44) := {1,2,3,4,5,9,10,12,13,14,15,16,17,18,19,20,21,22,23,24,25,29,30,32,33,34,35,36,37,38,39,40,41,42,43}
theorem setA_spec : supports witness ∪ leaves witness = setA := by decide
abbrev VertexA := {v : Fin 44 // v ∈ setA}
def graphA : SimpleGraph VertexA := witness.induce (setA : Set (Fin 44))
instance : DecidableRel graphA.Adj := inferInstanceAs
  (DecidableRel fun u v : VertexA => witness.Adj u.val v.val)
def labelA (v : VertexA) : Fin 13 := ![0,0,0,0,1,1,0,0,0,2,2,0,3,3,4,4,5,5,5,5,6,6,6,6,7,7,0,0,0,8,8,0,9,9,10,10,11,11,11,11,12,12,12,12] v.val
def repA (i : Fin 13) : VertexA := ⟨![1,4,9,12,14,16,20,24,29,32,34,36,40] i, by fin_cases i <;> decide⟩
theorem labelA_rep : ∀ i, labelA (repA i) = i := by decide
theorem labelA_adj : ∀ u v : VertexA, graphA.Adj u v → labelA u = labelA v := by decide
theorem componentsA_lower : 13 ≤ componentsOn witness (supports witness ∪ leaves witness) := by
  rw [componentsOn, setA_spec]
  exact labeled_components_lower graphA 13 labelA repA labelA_rep labelA_adj

def setB : Finset (Fin 44) := {4,6,7,11,12,13,14,15,16,18,19,20,22,23,24,26,27,31,32,33,34,35,36,38,39,40,42,43}
theorem setB_spec : closedNeighbors witness (degreeTwo witness) = setB := by decide
abbrev VertexB := {v : Fin 44 // v ∈ setB}
def graphB : SimpleGraph VertexB := witness.induce (setB : Set (Fin 44))
instance : DecidableRel graphB.Adj := inferInstanceAs
  (DecidableRel fun u v : VertexB => witness.Adj u.val v.val)
def labelB (v : VertexB) : Fin 8 := ![0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,2,0,2,2,3,0,3,3,4,0,4,4,0,0,0,5,5,5,5,5,6,0,6,6,7,0,7,7] v.val
def repB (i : Fin 8) : VertexB := ⟨![4,11,16,20,24,31,36,40] i, by fin_cases i <;> decide⟩
theorem labelB_rep : ∀ i, labelB (repB i) = i := by decide
theorem labelB_adj : ∀ u v : VertexB, graphB.Adj u v → labelB u = labelB v := by decide
theorem componentsB_lower : 8 ≤ componentsOn witness (closedNeighbors witness (degreeTwo witness)) := by
  rw [componentsOn, setB_spec]
  exact labeled_components_lower graphB 8 labelB repB labelB_rep labelB_adj

theorem conjecture351 : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj], T.IsTree → 2 < Fintype.card V →
      componentsOn T (supports T ∪ leaves T) +
        componentsOn T (closedNeighbors T (degreeTwo T)) ≤ T.totalDominationNumber := by
  intro h
  have hh := h (Fin 44) witness witness_tree (by decide)
  have hA := componentsA_lower
  have hB := componentsB_lower
  have ht := total_bound
  omega

end WOWII351Proof

#print axioms WOWII351Proof.witness_tree
#print axioms WOWII351Proof.componentsA_lower
#print axioms WOWII351Proof.componentsB_lower
#print axioms WOWII351Proof.total_bound
#print axioms WOWII351Proof.conjecture351
