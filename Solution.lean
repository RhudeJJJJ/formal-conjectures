module

public import WOWII161.Proof

/-! # Proved version of the independently stated WOWII161 challenge -/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture161

open SimpleGraph

/-- Every finite connected simple graph satisfies WOWII Conjecture 161. -/
theorem conjecture161 {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    (maxLocalIndependence Gᶜ : ℝ) ≤ Ls G :=
  conjecture161_proved G h_conn

end WrittenOnTheWallII.GraphConjecture161

