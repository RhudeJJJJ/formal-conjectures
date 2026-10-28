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

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section
namespace WOWII96
open SimpleGraph Finset
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A neighbour set may be lifted to the actual induced-neighbourhood graph. -/
theorem local_card_bound (v : V) (s : Finset V)
    (hs : G.IsIndepSet (s : Set V)) (hn : ∀ x ∈ s, G.Adj v x) :
    s.card ≤ indepNeighborsCard G v := by
  classical
  let t : Finset (G.neighborSet v) := s.subtype (fun x => x ∈ G.neighborSet v)
  have ht : (G.induce (G.neighborSet v)).IsIndepSet (t : Set (G.neighborSet v)) := by
    intro x hx y hy hne
    have hx' : x.val ∈ s := by simpa [t] using hx
    have hy' : y.val ∈ s := by simpa [t] using hy
    exact hs hx' hy' (fun he => hne (Subtype.ext he))
  have hb := ht.card_le_indepNum
  have hf : s.filter (G.Adj v) = s := Finset.filter_eq_self.mpr hn
  simpa only [t, Finset.card_subtype, SimpleGraph.mem_neighborSet, hf, indepNeighborsCard] using hb

omit [Fintype V] in
/-- Every non-root vertex has a neighbour one distance layer closer to the root. -/
theorem exists_parent (hc : G.Connected) (r x : V) (hx : x ≠ r) :
    ∃ p, G.Adj x p ∧ G.dist r p + 1 = G.dist r x := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x r
  cases p with
  | nil => exact (hx rfl).elim
  | @cons _ y _ hxy q =>
    refine ⟨y, hxy, ?_⟩
    have h₁ := G.dist_le q
    have h₂ := hc.dist_triangle (u := r) (v := y) (w := x)
    have he : G.dist y x = 1 := G.dist_eq_one_iff_adj.mpr hxy.symm
    rw [Walk.length_cons, G.dist_comm] at hp
    rw [G.dist_comm] at h₁
    omega

noncomputable def parent (hc : G.Connected) (r x : V) : V :=
  open scoped Classical in
  if hx : x = r then r else Classical.choose (exists_parent hc r x hx)

omit [Fintype V] in
theorem parent_spec (hc : G.Connected) (r x : V) (hx : x ≠ r) :
    G.Adj x (parent hc r x) ∧ G.dist r (parent hc r x) + 1 = G.dist r x := by
  classical
  simpa only [parent, dif_neg hx] using Classical.choose_spec (exists_parent hc r x hx)

theorem local_positive [Nontrivial V] (hc : G.Connected) (v : V) :
    1 ≤ indepNeighborsCard G v := by
  classical
  obtain ⟨x, hx⟩ := exists_ne v
  have hn : ∃ u, G.Adj v u := by
    obtain ⟨q, hq⟩ := hc.exists_walk_length_eq_dist v x
    cases q with
    | nil => exact (hx rfl).elim
    | @cons _ y _ hvy _ => exact ⟨y, hvy⟩
  obtain ⟨u, hu⟩ := hn
  simpa using local_card_bound v {u} (by simp [SimpleGraph.IsIndepSet]) (by simpa using hu)

end WOWII96
