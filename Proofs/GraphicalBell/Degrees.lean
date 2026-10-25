import Proofs.GraphicalBell.Partitions
import Proofs.GraphicalBell.Deletion
import Mathlib.Data.Nat.Choose.Basic

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

noncomputable def degreeSum (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ∑ v ∈ S, degreeOn G S v

noncomputable def sizeOn (G : SimpleGraph V) (S : Finset V) : ℕ := degreeSum G S / 2

open scoped Classical in
lemma degreeOn_insert {G : SimpleGraph V} {S : Finset V} {v : V} (hv : v ∉ S) (w : V) :
    degreeOn G (insert v S) w = degreeOn G S w + if G.Adj w v then 1 else 0 := by
  classical
  unfold degreeOn
  rw [Finset.filter_insert]
  by_cases hadj : G.Adj w v
  · rw [if_pos hadj, if_pos hadj, card_insert_of_notMem (by simp only [mem_filter]; exact fun h => hv h.1)]
  · rw [if_neg hadj, if_neg hadj, Nat.add_zero]

open scoped Classical in
omit [DecidableEq V] in
lemma degreeOn_sum (G : SimpleGraph V) (S : Finset V) (v : V) :
    degreeOn G S v = ∑ w ∈ S, if G.Adj v w then 1 else 0 := by
  classical
  simp [degreeOn]

lemma degreeSum_insert {G : SimpleGraph V} {S : Finset V} {v : V} (hv : v ∉ S) :
    degreeSum G (insert v S) = degreeSum G S + 2 * degreeOn G S v := by
  classical
  have hvv : ¬ G.Adj v v := G.loopless.irrefl v
  have hs : (∑ w ∈ S, if G.Adj w v then 1 else 0) = degreeOn G S v := by
    rw [degreeOn_sum]
    apply sum_congr rfl
    intro w _
    have he : G.Adj w v ↔ G.Adj v w := ⟨G.symm.symm _ _, G.symm.symm _ _⟩
    simp only [he]
  simp only [degreeSum, sum_insert hv, degreeOn_insert hv, if_neg hvv, Nat.add_zero,
    sum_add_distrib]
  rw [hs]
  omega

lemma sizeOn_insert {G : SimpleGraph V} {S : Finset V} {v : V} (hv : v ∉ S) :
    sizeOn G (insert v S) = sizeOn G S + degreeOn G S v := by
  unfold sizeOn
  rw [degreeSum_insert hv]
  omega

lemma degreeOn_le {G : SimpleGraph V} {S : Finset V} {v : V} (hv : v ∈ S) :
    degreeOn G S v ≤ S.card - 1 := by
  classical
  have hs : S.filter (G.Adj v) ⊆ S.erase v := by
    intro w hw
    refine mem_erase.mpr ⟨?_, (mem_filter.mp hw).1⟩
    intro he
    have hh := (mem_filter.mp hw).2
    rw [he] at hh
    exact G.loopless.irrefl v hh
  exact (card_le_card hs).trans_eq (card_erase_of_mem hv)

lemma degreeSum_le (G : SimpleGraph V) (S : Finset V) :
    degreeSum G S ≤ S.card * (S.card - 1) := by
  unfold degreeSum
  calc
    (∑ v ∈ S, degreeOn G S v) ≤ ∑ _v ∈ S, (S.card - 1) :=
      sum_le_sum fun v hv => degreeOn_le hv
    _ = S.card * (S.card - 1) := by simp

lemma sizeOn_le (G : SimpleGraph V) (S : Finset V) : sizeOn G S ≤ S.card.choose 2 := by
  unfold sizeOn
  rw [Nat.choose_two_right]
  exact Nat.div_le_div_right (degreeSum_le G S)

omit [DecidableEq V] in
lemma exists_small_degree {G : SimpleGraph V} {S : Finset V} {q : ℕ}
    (hq : q < S.card) (hm : sizeOn G S < (q + 1).choose 2) :
    ∃ v ∈ S, degreeOn G S v < q := by
  classical
  by_contra hn
  have hlow : ∀ v ∈ S, q ≤ degreeOn G S v := by
    intro v hv
    by_contra h
    exact hn ⟨v, hv, by omega⟩
  have hsum : S.card * q ≤ degreeSum G S := by
    unfold degreeSum
    calc
      S.card * q = ∑ _v ∈ S, q := by simp
      _ ≤ ∑ v ∈ S, degreeOn G S v := sum_le_sum fun v hv => hlow v hv
  have hmul : (q + 1) * q ≤ S.card * q := Nat.mul_le_mul_right q (by omega)
  have ht : 2 * sizeOn G S + 1 < (q + 1) * q := by
    rw [Nat.choose_two_right] at hm
    simp only [Nat.add_sub_cancel] at hm
    omega
  have hup : degreeSum G S ≤ 2 * sizeOn G S + 1 := by unfold sizeOn; omega
  omega

end GraphicalBellProof
