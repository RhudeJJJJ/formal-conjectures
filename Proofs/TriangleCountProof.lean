/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees
import Mathlib.Tactic

/-! Bijection between incident 3-cliques and edges inside the neighbor set.
Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization. -/
namespace TriangleCountProof
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangle_count (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.edgeFinset.filter fun e => e.toFinset ⊆ G.neighborFinset v).card =
      G.numTrianglesAtVertex v := by
  classical
  unfold numTrianglesAtVertex
  let E := G.edgeFinset.filter fun e => e.toFinset ⊆ G.neighborFinset v
  let T := (G.cliqueFinset 3).filter fun s => v ∈ s
  have hnot (e : Sym2 V) (he : e ∈ E) : v ∉ e.toFinset := by
    intro hv
    have := (mem_filter.mp he).2 hv
    exact G.irrefl (G.mem_neighborFinset v v |>.mp this)
  apply card_bij (s := E) (t := T) (fun e _ => insert v e.toFinset)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := (G.mem_edgeFinset).mp (mem_filter.mp he).1
      have hva : G.Adj v a := (G.mem_neighborFinset v a).mp
        ((mem_filter.mp he).2 (by simp [Sym2.toFinset_mk_eq]))
      have hvb : G.Adj v b := (G.mem_neighborFinset v b).mp
        ((mem_filter.mp he).2 (by simp [Sym2.toFinset_mk_eq]))
      apply mem_filter.mpr
      refine ⟨(G.mem_cliqueFinset_iff).mpr ⟨?_, ?_⟩, mem_insert_self _ _⟩
      · simp only [Sym2.toFinset_mk_eq, coe_insert, coe_singleton]
        apply (G.isClique_insert).mpr
        exact ⟨(G.isClique_pair).mpr (fun _ => hab), by
          intro w hw _; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl; exact hva; exact hvb⟩
      · rw [card_insert_of_notMem (hnot _ he),
          Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet (by simpa using (mem_filter.mp he).1))]
  · intro e he f hf h
    have hh := congrArg (fun s : Finset V => s.erase v) h
    rw [erase_insert (hnot e he), erase_insert (hnot f hf)] at hh
    apply Sym2.ext
    intro a
    simp only [← Sym2.mem_toFinset, hh]
  · intro s hs
    have hcl : G.IsNClique 3 s := (G.mem_cliqueFinset_iff).mp (mem_filter.mp hs).1
    have hv : v ∈ s := (mem_filter.mp hs).2
    have htwo : (s.erase v).card = 2 := by rw [card_erase_of_mem hv, hcl.card_eq]
    obtain ⟨a, b, hab, habset⟩ := card_eq_two.mp htwo
    have ha : a ∈ s := mem_of_mem_erase (habset ▸ (by simp : a ∈ ({a,b} : Finset V)))
    have hb : b ∈ s := mem_of_mem_erase (habset ▸ (by simp : b ∈ ({a,b} : Finset V)))
    have hva : v ≠ a := by
      have := mem_erase.mp (habset ▸ (by simp : a ∈ ({a,b} : Finset V)))
      exact this.1.symm
    have hvb : v ≠ b := by
      have := mem_erase.mp (habset ▸ (by simp : b ∈ ({a,b} : Finset V)))
      exact this.1.symm
    refine ⟨s(a,b), ?_, ?_⟩
    · apply mem_filter.mpr
      refine ⟨(G.mem_edgeFinset).mpr (hcl.isClique ha hb hab), ?_⟩
      intro w hw
      simp only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact (G.mem_neighborFinset _ _).mpr (hcl.isClique hv ha hva)
      · exact (G.mem_neighborFinset _ _).mpr (hcl.isClique hv hb hvb)
    · rw [Sym2.toFinset_mk_eq, ← habset, insert_erase hv]
end TriangleCountProof
