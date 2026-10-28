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
public import Proofs.WOWII72.Graph
public import Proofs.WOWII72.Attachment
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section
namespace WOWII72
open SimpleGraph Finset

/-- An acyclic graph has no triangle. -/
theorem no_triangle {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  classical
  have ht : G.IsNClique 3 ({a,b,c} : Finset V) :=
    G.is3Clique_triple_iff.mpr ⟨hab, hca.symm, hbc⟩
  exact hG.cliqueFree (by decide) _ ht

/-- Two distinct two-edge paths would form a four-cycle. -/
theorem no_four_cycle {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {a b c d : V} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) : False := by
  classical
  let p : G.Walk a c := .cons hab (.cons hbc .nil)
  let q : G.Walk a c := .cons hda.symm (.cons hcd.symm .nil)
  have hp : p.IsPath := by simp [p, Walk.cons_isPath_iff, hab.ne, hbc.ne, hac]
  have hq : q.IsPath := by simp [q, Walk.cons_isPath_iff, hda.ne.symm, hcd.ne.symm, hac]
  have he := hG.subsingleton_path a c |>.elim (⟨p,hp⟩ : G.Path a c) ⟨q,hq⟩
  have hs := congrArg (fun w : G.Path a c => w.val.snd) he
  exact hbd (by simpa [p, q, Walk.snd] using hs)

/-- A connected induced set meeting both sides contains the clique attachment. -/
theorem attachment_mem {s : Finset (Fin 31)} (ht : (H.induce (s : Set (Fin 31))).Connected)
    {a z : Fin 31} (ha : a ∈ s) (hz : z ∈ s) (haQ : a.val < 24) (hzQ : ¬ z.val < 24) :
    (24 : Fin 31) ∈ s := by
  classical
  by_cases hze : z = 24
  · simpa [hze] using hz
  let C : Set (Fin 31) := {v | v.val ≤ 24}
  have hclosed : WOWIIAttachment.ClosedExcept (G := H) C 24 := by
    intro u v hu hne hadj
    exact clique_exit u v hu hne hadj
  have hzout : z ∉ C := by
    dsimp [C]
    have hne : z.val ≠ 24 := by
      intro he
      exact hze (Fin.ext he)
    omega
  have hain : a ∈ C := by dsimp [C]; omega
  obtain ⟨p⟩ := ht ⟨z,hz⟩ ⟨a,ha⟩
  have hm := WOWIIAttachment.walk_hits_attachment hclosed
    (p.map (SimpleGraph.Embedding.induce (G := H) (s : Set (Fin 31))).toHom) hzout hain
  rw [Walk.support_map] at hm
  obtain ⟨w, _, hw⟩ := List.mem_map.mp hm
  change w.val = 24 at hw
  have hws : w.val ∈ s := Finset.mem_coe.mp w.property
  rwa [hw] at hws

/-- If a tree leaves the clique, it contains at most one of its vertices. -/
theorem clique_injective {s : Finset (Fin 31)} (ht : (H.induce (s : Set (Fin 31))).IsTree)
    (hz : ∃ z ∈ s, ¬ z.val < 24) :
    ∀ a ∈ s, ∀ b ∈ s, a.val < 24 → b.val < 24 → a = b := by
  classical
  intro a ha b hb haQ hbQ
  by_contra hab
  obtain ⟨z, hzs, hzQ⟩ := hz
  have hat := attachment_mem ht.connected ha hzs haQ hzQ
  exact no_triangle ht.isAcyclic
    (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) (c := ⟨24,hat⟩)
    (clique_edges a b haQ hbQ hab) (clique_attachment b hbQ) (clique_attachment a haQ).symm

/-- A connected induced set of order at least two has a neighbour at every vertex. -/
theorem neighbour_in_set {s : Finset (Fin 31)} (hc : (H.induce (s : Set (Fin 31))).Connected)
    (hs : 1 < s.card) (a : Fin 31) (ha : a ∈ s) : ∃ b ∈ s, H.Adj a b := by
  classical
  obtain ⟨b,hb,hba⟩ := Finset.exists_mem_ne hs a
  obtain ⟨p⟩ := hc ⟨a,ha⟩ ⟨b,hb⟩
  cases p with
  | nil => exact (hba rfl).elim
  | @cons _ c _ hac _ => exact ⟨c.val, c.property, hac⟩

/-- Every actual induced tree in the 31-vertex graph has at most five vertices. -/
theorem tree_card_le_five (s : Finset (Fin 31))
    (ht : (H.induce (s : Set (Fin 31))).IsTree) : s.card ≤ 5 := by
  classical
  by_contra hn
  have hs : 5 < s.card := by omega
  by_cases hall : ∀ a ∈ s, a.val < 24
  · obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp (show 2 < s.card by omega)
    exact no_triangle ht.isAcyclic (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) (c := ⟨c,hc⟩)
      (clique_edges a b (hall a ha) (hall b hb) hab)
      (clique_edges b c (hall b hb) (hall c hc) hbc)
      (clique_edges c a (hall c hc) (hall a ha) hac.symm)
  · have hz : ∃ z ∈ s, ¬ z.val < 24 := by
      by_contra hnz
      apply hall
      intro z hz
      by_contra hlt
      exact hnz ⟨z,hz,hlt⟩
    have hqi := clique_injective ht hz
    have hinj : Set.InjOn project (s : Set (Fin 31)) := by
      intro a ha b hb he
      rcases (project_equal a b).mp he with he | he
      · exact he
      · exact hqi a ha b hb he.1 he.2
    have hcard : (s.image project).card = s.card := Finset.card_image_iff.mpr hinj
    have hfaith {a b : Fin 31} (ha : a ∈ s) (hb : b ∈ s) :
        small.Adj (project a) (project b) ↔ H.Adj a b := by
      by_cases hab : a = b
      · subst b; simp
      · exact (project_adj a b (fun he => hab (hinj ha hb he))).symm
    have hobs := small_obstruction (s.image project) (by omega)
    rcases hobs with htri | hfour | hiso
    · obtain ⟨a,ha,b,hb,c,hc,hab,hbc,hca⟩ := htri
      obtain ⟨a',ha',hea⟩ := Finset.mem_image.mp ha
      obtain ⟨b',hb',heb⟩ := Finset.mem_image.mp hb
      obtain ⟨c',hc',hec⟩ := Finset.mem_image.mp hc
      exact no_triangle ht.isAcyclic (a := ⟨a',ha'⟩) (b := ⟨b',hb'⟩) (c := ⟨c',hc'⟩)
        ((hfaith ha' hb').mp (by simpa [hea,heb] using hab))
        ((hfaith hb' hc').mp (by simpa [heb,hec] using hbc))
        ((hfaith hc' ha').mp (by simpa [hec,hea] using hca))
    · obtain ⟨a,ha,b,hb,c,hc,d,hd,hac,hbd,hab,hbc,hcd,hda⟩ := hfour
      obtain ⟨a',ha',hea⟩ := Finset.mem_image.mp ha
      obtain ⟨b',hb',heb⟩ := Finset.mem_image.mp hb
      obtain ⟨c',hc',hec⟩ := Finset.mem_image.mp hc
      obtain ⟨d',hd',hed⟩ := Finset.mem_image.mp hd
      have hac' : (⟨a',ha'⟩ : (s : Set (Fin 31))) ≠ ⟨c',hc'⟩ := by
        intro he
        have hv := congrArg (fun v : (s : Set (Fin 31)) => project v.val) he
        exact hac (by simpa [hea,hec] using hv)
      have hbd' : (⟨b',hb'⟩ : (s : Set (Fin 31))) ≠ ⟨d',hd'⟩ := by
        intro he
        have hv := congrArg (fun v : (s : Set (Fin 31)) => project v.val) he
        exact hbd (by simpa [heb,hed] using hv)
      exact no_four_cycle ht.isAcyclic hac' hbd'
        ((hfaith ha' hb').mp (by simpa [hea,heb] using hab))
        ((hfaith hb' hc').mp (by simpa [heb,hec] using hbc))
        ((hfaith hc' hd').mp (by simpa [hec,hed] using hcd))
        ((hfaith hd' ha').mp (by simpa [hed,hea] using hda))
    · obtain ⟨a,ha,hiso⟩ := hiso
      obtain ⟨a',ha',hea⟩ := Finset.mem_image.mp ha
      obtain ⟨b',hb',hab⟩ := neighbour_in_set ht.connected (by omega) a' ha'
      have hadj := (hfaith ha' hb').mpr hab
      exact hiso (project b') (Finset.mem_image.mpr ⟨b',hb',rfl⟩) (by simpa [hea] using hadj)

/-- Upper bound on the repository's actual largest-induced-tree invariant. -/
theorem tree_upper : largestInducedTreeSize H ≤ 5 := by
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨s, rfl, hs⟩
  exact tree_card_le_five s hs

end WOWII72
