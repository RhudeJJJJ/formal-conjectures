/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.

Statement transport for the separately attributed Ramazan Kara / Robert
Sneiderman r=5 formalization. The standalone transport theorem has an
explicit fixed-case hypothesis and is not itself the r=5 proof.
-/
import Erdos617.Basic
import Mathlib.Tactic

namespace Gebendorfer.Erdos617R5

/-- Transfer the loop-free finite formulation to the upstream Sym2 statement. -/
theorem transport (hfive : Erdos617.Problem617At 5)
    {V : Type*} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 26) (coloring : Sym2 V → Fin 5) :
    ∃ (S : Finset V) (k : Fin 5), S.card = 6 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u,v) ≠ k := by
  classical
  let e : Fin 26 ≃ V := (Fintype.equivFinOfCardEq hV).symm
  let χ : Erdos617.EdgeColoring (Fin 26) (Fin 5) :=
    fun edge => coloring (Sym2.map e edge.val)
  obtain ⟨S, hS, k, hk⟩ := hfive χ
  refine ⟨S.map e.toEmbedding, k, ?_, ?_⟩
  · simpa using hS
  · intro u hu v hv huv hc
    rw [Finset.mem_map] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have hab : a ≠ b := fun h => huv (congrArg e h)
    apply hk
    refine ⟨a, ha, b, hb, hab, ?_⟩
    simpa [χ, SimpleGraph.EdgeLabeling.get] using hc

#print axioms transport

end Gebendorfer.Erdos617R5
