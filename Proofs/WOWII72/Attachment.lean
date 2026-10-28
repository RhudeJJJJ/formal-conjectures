/-
Copyright 2026 Jonas J. Gebendorfer.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

@[expose] public section
namespace WOWIIAttachment
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- A set whose only possible exit is at c. -/
def ClosedExcept (S : Set V) (c : V) : Prop :=
  ∀ ⦃u v⦄, u ∈ S → u ≠ c → G.Adj u v → v ∈ S

/-- Any walk entering such a set from outside visits its attachment vertex. -/
theorem walk_hits_attachment {S : Set V} {c u v : V}
    (hS : ClosedExcept (G := G) S c) (p : G.Walk u v) (hu : u ∉ S) (hv : v ∈ S) :
    c ∈ p.support := by
  induction p with
  | nil => exact (hu hv).elim
  | @cons u w v huw p ih =>
    by_cases hw : w ∈ S
    · have hwc : w = c := by
        by_contra hne
        exact hu (hS hw hne huw.symm)
      have hm : c ∈ p.support := hwc ▸ p.start_mem_support
      exact List.mem_cons_of_mem u hm
    · exact List.mem_cons_of_mem u (ih hw hv)

/-- A simple path cannot leave and re-enter through its sole attachment. -/
theorem path_stays_closedExcept {S : Set V} {c u v : V}
    (hS : ClosedExcept (G := G) S c) (p : G.Walk u v) (hp : p.IsPath)
    (hu : u ∈ S) (hv : v ∈ S) : ∀ w ∈ p.support, w ∈ S := by
  induction p with
  | nil => simpa using hu
  | @cons u w v huw p ih =>
    have hw : w ∈ S := by
      by_contra hn
      have huc : u = c := by
        by_contra hne
        exact hn (hS hu hne huw)
      have hc := walk_hits_attachment hS p hn hv
      have hnot := (Walk.cons_isPath_iff _ _).mp hp |>.2
      exact hnot (huc ▸ hc)
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hu
    · exact ih hp.of_cons hw hv z hz

/-- Distances in an induced connected subgraph cannot be shorter. -/
theorem dist_le_induce_dist {S : Set V} (hc : (G.induce S).Connected)
    (u v : S) : G.dist u.val v.val ≤ (G.induce S).dist u v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  have hb := G.dist_le (p.map (SimpleGraph.Embedding.induce (G := G) S).toHom)
  change G.dist u.val v.val ≤ (p.map (SimpleGraph.Embedding.induce (G := G) S).toHom).length at hb
  simpa only [Walk.length_map, hp] using hb

/-- A one-attachment side of a connected graph stays connected. -/
theorem connected_closedExcept (hc : G.Connected) {S : Set V} {c : V}
    (hS : ClosedExcept (G := G) S c) (hn : S.Nonempty) : (G.induce S).Connected := by
  let : Nonempty S := hn.to_subtype
  constructor
  intro u v
  obtain ⟨p, hp⟩ := hc.exists_isPath u.val v.val
  exact ⟨p.induce S (path_stays_closedExcept hS p hp u.property v.property)⟩

/-- Removing the other one-attachment sides preserves all internal distances. -/
theorem induce_dist_eq_of_closedExcept (hc : G.Connected) {S : Set V} {c : V}
    (hS : ClosedExcept (G := G) S c) (u v : S) :
    (G.induce S).dist u v = G.dist u.val v.val := by
  have hconn := connected_closedExcept hc hS ⟨u.val, u.property⟩
  apply le_antisymm
  · obtain ⟨p, hp, hlen⟩ := hc.exists_path_of_dist u.val v.val
    let q := p.induce S (path_stays_closedExcept hS p hp u.property v.property)
    have hb := (G.induce S).dist_le q
    have hmap := Walk.map_induce p (path_stays_closedExcept hS p hp u.property v.property)
    have hl := congrArg (fun w : G.Walk u.val v.val => w.length) hmap
    have hql : q.length = p.length := by
      change (q.map (SimpleGraph.Embedding.induce (G := G) S).toHom).length = p.length at hl
      rw [Walk.length_map] at hl
      exact hl
    change (G.induce S).dist u v ≤ q.length at hb
    simpa only [hql, hlen] using hb
  · exact dist_le_induce_dist hconn u v

end WOWIIAttachment
