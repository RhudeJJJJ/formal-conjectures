/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanForkResidual

/-!
# Label the actual nonroot vertices of a pendant path

The arm labels enumerate the tail of the given walk. In an acyclic graph its
walk subgraph is the graph induced on its vertices. A positive simple path
therefore gives an induced path embedding whose zero label is its first neighbor.
Source: the actual-fork checkpoint b546e3edbad3e45182649bc798182bf30a7457fe,
and Mathlib's `Walk.IsPath.pathGraphIsoToSubgraph`.
-/

namespace Gebendorfer.RadenkovicGutman.ArmEmbedding

open SimpleGraph
open scoped Classical
noncomputable section
variable {V : Type*} {G : SimpleGraph V}

theorem walk_subgraph_induced (hA : G.IsAcyclic) {u v : V} (p : G.Walk u v) :
    p.toSubgraph.coe = G.induce p.toSubgraph.verts := by
  have hle : p.toSubgraph.coe ≤ G.induce p.toSubgraph.verts := by
    intro x y h
    exact p.toSubgraph.coe_adj_sub x y h
  have hT : (G.induce p.toSubgraph.verts).IsTree :=
    ⟨p.toSubgraph_connected.mono hle, hA.induce _⟩
  exact le_antisymm hle
    ((isTree_iff_minimal_connected.mp hT).2 p.toSubgraph_connected hle)

theorem mem_tail_iff {u v x : V} (p : G.Walk u v) (hp : p.IsPath)
    (hpos : 0 < p.length) : x ∈ p.tail.support ↔ x ∈ p.support ∧ x ≠ u := by
  have hn : ¬p.Nil := Walk.not_nil_iff_lt_length.mpr hpos
  have hnd : (u :: p.tail.support).Nodup := by
    rw [Walk.cons_support_tail hn]
    exact hp.support_nodup
  have hu : u ∉ p.tail.support := (List.nodup_cons.mp hnd).1
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [← Walk.cons_support_tail hn]
      exact List.mem_cons_of_mem u hx
    · intro he
      exact hu (he ▸ hx)
  · rintro ⟨hx, hxu⟩
    rw [← Walk.cons_support_tail hn, List.mem_cons] at hx
    exact hx.resolve_left hxu

/-- The labels enumerate this walk's tail, in order from the attachment point. -/
def armVertex {u v : V} (p : G.Walk u v) (i : Fin (p.tail.length + 1)) : V :=
  (p.tail.pathGraphHomToSubgraph i).val

theorem armVertex_mem_tail {u v : V} (p : G.Walk u v) (i : Fin (p.tail.length + 1)) :
    armVertex p i ∈ p.tail.support :=
  p.tail.mem_verts_toSubgraph.mp (p.tail.pathGraphHomToSubgraph i).property

theorem armVertex_mem {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hpos : 0 < p.length) (i : Fin (p.tail.length + 1)) : armVertex p i ∈ p.support :=
  ((mem_tail_iff p hp hpos).mp (armVertex_mem_tail p i)).1

theorem armVertex_ne_root {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hpos : 0 < p.length) (i : Fin (p.tail.length + 1)) : armVertex p i ≠ u :=
  ((mem_tail_iff p hp hpos).mp (armVertex_mem_tail p i)).2

theorem armVertex_zero {u v : V} (p : G.Walk u v) : armVertex p 0 = p.snd := by
  simp [armVertex, Walk.pathGraphHomToSubgraph]

theorem armVertex_injective {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    Function.Injective (armVertex p) := by
  intro i j hij
  exact hp.tail.pathGraphIsoToSubgraph.injective (Subtype.ext hij)

theorem armVertex_range {u v x : V} (p : G.Walk u v) (hp : p.IsPath)
    (hpos : 0 < p.length) (hx : x ∈ p.support) (hxu : x ≠ u) :
    ∃ i, armVertex p i = x := by
  have ht := (mem_tail_iff p hp hpos).mpr ⟨hx, hxu⟩
  obtain ⟨i, hi⟩ := hp.tail.pathGraphIsoToSubgraph.surjective
    ⟨x, p.tail.mem_verts_toSubgraph.mpr ht⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem armVertex_adj_iff (hA : G.IsAcyclic) {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (i j : Fin (p.tail.length + 1)) :
    G.Adj (armVertex p i) (armVertex p j) ↔ (pathGraph (p.tail.length + 1)).Adj i j := by
  let f := hp.tail.pathGraphIsoToSubgraph
  have hle : G.induce p.tail.toSubgraph.verts ≤ p.tail.toSubgraph.coe :=
    (walk_subgraph_induced hA p.tail).symm.le
  change G.Adj ((f i).val) ((f j).val) ↔ _
  constructor
  · intro h
    exact f.map_rel_iff.mp (hle h)
  · intro h
    exact p.tail.toSubgraph.coe_adj_sub _ _ (f.map_rel_iff.mpr h)

theorem root_arm_adj_iff (hA : G.IsAcyclic) {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (hpos : 0 < p.length) (i : Fin (p.tail.length + 1)) :
    G.Adj u (armVertex p i) ↔ i = 0 := by
  constructor
  · intro h
    have he := hA.eq_snd_of_adj_start hp h (armVertex_mem p hp hpos i)
    apply armVertex_injective p hp
    exact he.trans (armVertex_zero p).symm
  · rintro rfl
    rw [armVertex_zero]
    exact p.adj_snd (Walk.not_nil_iff_lt_length.mpr hpos)

#print axioms walk_subgraph_induced
#print axioms mem_tail_iff
#print axioms armVertex_mem_tail
#print axioms armVertex_mem
#print axioms armVertex_ne_root
#print axioms armVertex_zero
#print axioms armVertex_injective
#print axioms armVertex_range
#print axioms armVertex_adj_iff
#print axioms root_arm_adj_iff

end
end Gebendorfer.RadenkovicGutman.ArmEmbedding
