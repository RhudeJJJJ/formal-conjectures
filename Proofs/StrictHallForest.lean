import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-!
# Strict Hall selections with a decreasing rank

Auxiliary construction for Gebendorfer's WOWII 412d manuscript, Lemma 5.
A system of distinct representatives is supplemented with a second choice
whose matched predecessor has smaller rank. No graph-theoretic conclusion
or total-domination bound is assumed here.
-/
namespace StrictHallForest
open Finset
variable {I W : Type*} [DecidableEq I] [DecidableEq W]

omit [DecidableEq I] in
/-- Strict Hall supplies an incidence escaping the representatives of a
nonempty subfamily. The representatives need not be injective for this step. -/
lemma exists_escape (E : I → Finset W) (f : I → W)
    (hHall : ∀ S : Finset I, S.Nonempty → S.card + 1 ≤ (S.biUnion E).card)
    (S : Finset I) (hne : S.Nonempty) :
    ∃ i ∈ S, ∃ w ∈ E i, w ∉ S.image f := by
  have hc := hHall S hne
  have hi := card_image_le (s := S) (f := f)
  have hn : ¬ S.biUnion E ⊆ S.image f := by
    intro hs
    have := card_le_card hs
    omega
  obtain ⟨w, hw, hwo⟩ := not_subset.mp hn
  obtain ⟨i, hi, hwi⟩ := mem_biUnion.mp hw
  exact ⟨i, hi, w, hwi, hwo⟩

/-- Eliminate an escaping index first. The remaining indices get larger
ranks, so every second choice either leaves the matching or decreases rank. -/
lemma exists_rank_on (E : I → Finset W) (f : I → W)
    (hHall : ∀ S : Finset I, S.Nonempty → S.card + 1 ≤ (S.biUnion E).card)
    (S : Finset I) :
    ∃ rank : I → ℕ, ∀ i ∈ S, ∃ w ∈ E i,
      w ≠ f i ∧ ∀ j ∈ S, f j = w → rank j < rank i := by
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hne : S.Nonempty
  · obtain ⟨i, hi, w, hwi, hwo⟩ := exists_escape E f hHall S hne
    obtain ⟨rank, hrank⟩ := ih (S.erase i) (erase_ssubset hi)
    refine ⟨fun j => if j = i then 0 else rank j + 1, ?_⟩
    intro j hj
    by_cases hji : j = i
    · subst j
      refine ⟨w, hwi, ?_, ?_⟩
      · intro he
        exact hwo (mem_image.mpr ⟨i, hi, he.symm⟩)
      · intro k hk hkw
        exact False.elim (hwo (mem_image.mpr ⟨k, hk, hkw⟩))
    · obtain ⟨v, hv, hvj, hvlt⟩ := hrank j (mem_erase.mpr ⟨hji, hj⟩)
      refine ⟨v, hv, hvj, ?_⟩
      intro k hk hkv
      by_cases hki : k = i
      · simp [hki, hji]
      · have := hvlt k (mem_erase.mpr ⟨hki, hk⟩) hkv
        simp only [hki, hji, if_false]
        omega
  · refine ⟨fun _ => 0, ?_⟩
    intro i hi
    exact False.elim (hne ⟨i, hi⟩)

/-- Strict Hall yields distinct representatives and second representatives
with a strict descent along all matched predecessors. -/
theorem exists_ranked_selection [Fintype I] (E : I → Finset W)
    (hHall : ∀ S : Finset I, S.Nonempty → S.card + 1 ≤ (S.biUnion E).card) :
    ∃ f p : I → W, ∃ rank : I → ℕ,
      Function.Injective f ∧
      (∀ i, f i ∈ E i) ∧
      (∀ i, p i ∈ E i ∧ p i ≠ f i) ∧
      ∀ i j, f j = p i → rank j < rank i := by
  classical
  have hweak : ∀ S : Finset I, S.card ≤ (S.biUnion E).card := by
    intro S
    by_cases hne : S.Nonempty
    · exact (Nat.le_succ _).trans (hHall S hne)
    · simp [not_nonempty_iff_eq_empty.mp hne]
  obtain ⟨f, hf, hfm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' E).mp hweak
  obtain ⟨rank, hrank⟩ := exists_rank_on E f hHall univ
  have hh : ∀ i, ∃ w ∈ E i, w ≠ f i ∧
      ∀ j, f j = w → rank j < rank i := by simpa using hrank
  choose p hpm hpf hpr using hh
  exact ⟨f, p, rank, hf, hfm, fun i => ⟨hpm i, hpf i⟩, hpr⟩

/-- Extend the index rank to the ground set; unmatched vertices have rank zero. -/
noncomputable def vertexRank (f : I → W) (rank : I → ℕ) (w : W) : ℕ := by
  classical
  exact if h : ∃ i, f i = w then rank h.choose + 1 else 0

omit [DecidableEq I] [DecidableEq W] in
lemma vertexRank_apply (f : I → W) (rank : I → ℕ) (hf : Function.Injective f) (i : I) :
    vertexRank f rank (f i) = rank i + 1 := by
  classical
  unfold vertexRank
  split_ifs with h
  · rw [hf h.choose_spec]
  · exact False.elim (h ⟨i, rfl⟩)

omit [DecidableEq I] [DecidableEq W] in
lemma vertexRank_parent (f p : I → W) (rank : I → ℕ) (hf : Function.Injective f)
    (hr : ∀ i j, f j = p i → rank j < rank i) (i : I) :
    vertexRank f rank (p i) < vertexRank f rank (f i) := by
  classical
  rw [vertexRank_apply f rank hf]
  unfold vertexRank
  split_ifs with h
  · have := hr i h.choose h.choose_spec
    omega
  · omega

/-- A rank orientation with at most one descending neighbor has no cycles. -/
lemma isAcyclic_of_unique_lower_neighbor (G : SimpleGraph W) (rank : W → ℕ)
    (hne : ∀ u v, G.Adj u v → rank u ≠ rank v)
    (hunique : ∀ u v w, G.Adj u v → G.Adj u w →
      rank v < rank u → rank w < rank u → v = w) : G.IsAcyclic := by
  intro u c hc
  obtain ⟨w, hw, hmax⟩ := exists_max_image c.support.toFinset rank
    ⟨u, by simp⟩
  have hwc : w ∈ c.support := List.mem_toFinset.mp hw
  let d := c.rotate w hwc
  have hd : d.IsCycle := hc.rotate hwc
  have hds : rank d.snd ≤ rank w := by
    apply hmax
    apply List.mem_toFinset.mpr
    exact (c.mem_support_rotate_iff w hwc).mp (d.getVert_mem_support 1)
  have hdp : rank d.penultimate ≤ rank w := by
    apply hmax
    apply List.mem_toFinset.mpr
    exact (c.mem_support_rotate_iff w hwc).mp (d.getVert_mem_support (d.length - 1))
  have hs : G.Adj w d.snd := d.adj_snd hd.not_nil
  have hp : G.Adj w d.penultimate := (d.adj_penultimate hd.not_nil).symm
  have hsn := hne w d.snd hs
  have hpn := hne w d.penultimate hp
  exact hd.snd_ne_penultimate (hunique w d.snd d.penultimate hs hp (by omega) (by omega))

/-- The undirected graph formed by the two representatives of each index. -/
def selectionGraph (f p : I → W) (hpf : ∀ i, p i ≠ f i) : SimpleGraph W where
  Adj u v := ∃ i, (u = f i ∧ v = p i) ∨ (u = p i ∧ v = f i)
  symm := ⟨by
    rintro u v ⟨i, h | h⟩
    · exact ⟨i, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨i, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨by
    rintro u ⟨i, h | h⟩
    · exact hpf i (h.2.symm.trans h.1)
    · exact hpf i (h.1.symm.trans h.2)⟩

omit [DecidableEq I] in
lemma selectionGraph_isAcyclic (f p : I → W) (rank : I → ℕ)
    (hf : Function.Injective f) (hpf : ∀ i, p i ≠ f i)
    (hr : ∀ i j, f j = p i → rank j < rank i) :
    (selectionGraph f p hpf).IsAcyclic := by
  let R := vertexRank f rank
  have hd (i : I) : R (p i) < R (f i) := vertexRank_parent f p rank hf hr i
  apply isAcyclic_of_unique_lower_neighbor _ R
  · rintro u v ⟨i, h | h⟩ <;> rcases h with ⟨rfl, rfl⟩
    · exact (hd i).ne'
    · exact (hd i).ne
  · intro u v w huv huw hv hw
    obtain ⟨i, hi | hi⟩ := huv
    · obtain ⟨j, hj | hj⟩ := huw
      · have hij : i = j := hf (hi.1.symm.trans hj.1)
        exact hi.2.trans (hij ▸ hj.2.symm)
      · have := hd j
        rw [← hj.1, ← hj.2] at this
        omega
    · have := hd i
      rw [← hi.1, ← hi.2] at this
      omega

omit [DecidableEq I] [DecidableEq W] in
/-- Distinct indices yield distinct unordered edges, so passing to a simple
graph does not silently discard parallel indexed edges. -/
lemma selection_edges_injective (f p : I → W) (rank : I → ℕ)
    (hf : Function.Injective f)
    (hr : ∀ i j, f j = p i → rank j < rank i) :
    Function.Injective (fun i => s(f i, p i)) := by
  intro i j hij
  rcases Sym2.eq_iff.mp hij with h | h
  · exact hf h.1
  · have hi := hr i j h.2.symm
    have hj := hr j i h.1
    omega

/-- The strict Hall forest selection (the pair-selection part of Lemma 5).
Each index supplies two distinct incident vertices, and all selected pairs
form an acyclic simple graph with no repeated indexed edges. -/
theorem exists_forest_selection [Fintype I] (E : I → Finset W)
    (hHall : ∀ S : Finset I, S.Nonempty → S.card + 1 ≤ (S.biUnion E).card) :
    ∃ f p : I → W, ∃ hpf : ∀ i, p i ≠ f i,
      Function.Injective f ∧ (∀ i, f i ∈ E i ∧ p i ∈ E i) ∧
      (selectionGraph f p hpf).IsAcyclic ∧
      Function.Injective (fun i => s(f i, p i)) := by
  obtain ⟨f, p, rank, hf, hfm, hpm, hr⟩ := exists_ranked_selection E hHall
  exact ⟨f, p, fun i => (hpm i).2, hf, fun i => ⟨hfm i, (hpm i).1⟩,
    ⟨selectionGraph_isAcyclic f p rank hf (fun i => (hpm i).2) hr,
      selection_edges_injective f p rank hf hr⟩⟩

end StrictHallForest
