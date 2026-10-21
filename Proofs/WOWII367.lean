import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture367

open SimpleGraph

/-- Number of vertices of ambient degree $j$. -/
def degreeCount {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) : ℕ :=
  (Finset.univ.filter fun v => G.degree v = j).card

/-- Number of distinct ambient degrees. -/
def distinctDegreeCount {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image G.degree).card

/-- Degree two is a mode, allowing a tie with any other degree. -/
def TwoIsMode {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, degreeCount G (G.degree v) ≤ degreeCount G 2

/-- Degree two is the unique mode. -/
def TwoIsUniqueMode {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  0 < degreeCount G 2 ∧
    ∀ v, G.degree v ≠ 2 → degreeCount G (G.degree v) < degreeCount G 2

/-- The reading that permits tied modes. Multiplication clears the denominator. -/
def tiedModeStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V → TwoIsMode G →
      4 * distinctDegreeCount G ≤ 3 * G.totalDominationNumber

private theorem path_four_tree : (pathGraph 4).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected 3, ?_⟩
  have he : (pathGraph 4).edgeFinset.card = 3 := by decide
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, he,
    Nat.card_eq_fintype_card]
  decide

private theorem path_four_total_upper : (pathGraph 4).totalDominationNumber ≤ 2 := by
  apply csInf_le (OrderBot.bddBelow _)
  refine ⟨({1, 2} : Finset (Fin 4)), ?_⟩
  constructor
  · change ∀ v : Fin 4, ∃ w ∈ ({1, 2} : Finset (Fin 4)), (pathGraph 4).Adj v w
    decide
  · decide

/-- The tied-mode reading is false: the four-vertex path has two degree-one
vertices, two degree-two vertices, and a total dominating set of size two. -/
theorem not_tied_mode_statement : ¬ tiedModeStatement := by
  intro h
  have hm : TwoIsMode (pathGraph 4) := by decide
  have hd : distinctDegreeCount (pathGraph 4) = 2 := by decide
  have hb := h (Fin 4) (pathGraph 4) path_four_tree (by decide) hm
  rw [hd] at hb
  have hu := path_four_total_upper
  omega

end WrittenOnTheWallII.GraphConjecture367

#print axioms WrittenOnTheWallII.GraphConjecture367.not_tied_mode_statement
