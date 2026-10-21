import FormalConjectures.WrittenOnTheWallII.GraphConjecture348
import FormalConjectures.WrittenOnTheWallII.GraphConjecture367

/-!
General tree bounds for WOWII 348 and the positive reading of WOWII 367.
The proofs follow the written arguments of Jonas J. Gebendorfer, with Lean assistance
from OpenAI Codex. This development file is not a completed certificate until all
of its exported target theorems and their axiom audits compile.
-/

open Finset SimpleGraph

namespace WOWIITreeProof

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def rowSum (S T : Finset V) : ℕ :=
  ∑ v ∈ S, (G.neighborFinset v ∩ T).card

lemma neighbor_inter_card (v : V) (T : Finset V) :
    (G.neighborFinset v ∩ T).card = ∑ w ∈ T, if G.Adj v w then 1 else 0 := by
  simp only [Finset.sum_boole]
  congr 1
  ext w
  simp [and_comm]

lemma row_sum_comm (S T : Finset V) : rowSum G S T = rowSum G T S := by
  simp only [rowSum, neighbor_inter_card]
  rw [Finset.sum_comm]
  simp only [G.adj_comm]

lemma degree_split (v : V) (D : Finset V) :
    G.degree v = (G.neighborFinset v ∩ D).card +
      (G.neighborFinset v ∩ Dᶜ).card := by
  rw [← G.card_neighborFinset_eq_degree]
  have hi : G.neighborFinset v ∩ Dᶜ = G.neighborFinset v \ D := by
    ext w
    simp
  rw [hi, Finset.card_inter_add_card_sdiff]

lemma internal_sum_even (D : Finset V) : Even (rowSum G D D) := by
  classical
  let H := G.induce (D : Set V)
  have he : ∀ v : (D : Set V),
      H.degree v = (G.neighborFinset v ∩ D).card := by
    intro v
    have hm := G.map_neighborFinset_induce (s := (D : Set V)) v
    have hc := congrArg Finset.card hm
    simpa [H] using hc
  have hs : rowSum G D D = ∑ v : (D : Set V), H.degree v := by
    simp only [rowSum, he]
    exact (Finset.sum_coe_sort D _).symm
  rw [hs, H.sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

lemma row_sum_lower (D : Finset V) (hD : G.IsTotalDominating (D : Set V))
    (S : Finset V) : S.card ≤ rowSum G S D := by
  calc
    S.card = ∑ _ ∈ S, 1 := by simp
    _ ≤ rowSum G S D := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨w, hw, hadj⟩ := hD v
      exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
        ⟨w, by simp [hw, hadj]⟩)

def nonleaves : Finset V := Finset.univ.filter fun v => G.degree v ≠ 1

lemma total_degree_lower (D : Finset V) (hD : G.IsTotalDominating (D : Set V))
    (S : Finset V) : S.card + (S.filter fun v => G.degree v ≠ 1).card ≤
      ∑ v ∈ S, G.degree v := by
  have hpos (v : V) : 1 ≤ G.degree v := by
    obtain ⟨w, hw, hadj⟩ := hD v
    exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
      ⟨w, by simpa using hadj⟩)
  calc
    S.card + (S.filter fun v => G.degree v ≠ 1).card =
        ∑ v ∈ S, (1 + if G.degree v ≠ 1 then 1 else 0) := by
      simp [Finset.sum_add_distrib, Finset.sum_boole]
    _ ≤ ∑ v ∈ S, G.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      have hp := hpos v
      split_ifs <;> omega

lemma nonleaf_internal_bound (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) :
    (nonleaves G).card + rowSum G D D + 2 ≤ 3 * D.card := by
  classical
  have ht := hT.card_edgeFinset
  have handshake := G.sum_degrees_eq_twice_card_edges
  have hpartition := Finset.sum_add_sum_compl D (fun v => G.degree v)
  have hcard := Finset.card_add_card_compl D
  have hcross := row_sum_lower G D hD Dᶜ
  have hswap := row_sum_comm G D Dᶜ
  have hsplit : (∑ v ∈ D, G.degree v) = rowSum G D D + rowSum G D Dᶜ := by
    simp only [rowSum, ← Finset.sum_add_distrib, ← degree_split]
  have hx := total_degree_lower G D hD Dᶜ
  have hn : (nonleaves G).card ≤ D.card +
      (Dᶜ.filter fun v => G.degree v ≠ 1).card := by
    apply (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro v hv
    by_cases hd : v ∈ D
    · exact Finset.mem_union_left _ hd
    · exact Finset.mem_union_right _ (by simpa [nonleaves, hd] using hv)
  simp only [Finset.sum_univ] at handshake hpartition
  omega

lemma positive_degree (D : Finset V) (hD : G.IsTotalDominating (D : Set V))
    (v : V) : 1 ≤ G.degree v := by
  obtain ⟨w, hw, hadj⟩ := hD v
  exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
    ⟨w, by simpa using hadj⟩)

lemma leaf_identity (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) :
    (Finset.univ.filter fun v => G.degree v = 1).card =
      2 + ∑ v : V, (G.degree v - 2) := by
  have ht := hT.card_edgeFinset
  have handshake := G.sum_degrees_eq_twice_card_edges
  have hp (v : V) : G.degree v + (if G.degree v = 1 then 1 else 0) =
      2 + (G.degree v - 2) := by
    have := positive_degree G D hD v
    split_ifs <;> omega
  have hs := Finset.sum_congr (s := (Finset.univ : Finset V)) rfl (fun v _ => hp v)
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hs
  omega

lemma triangular_lower (S : Finset ℕ) (hS : ∀ a ∈ S, 3 ≤ a) :
    S.card * (S.card + 1) ≤ 2 * ∑ a ∈ S, (a - 2) := by
  classical
  induction S using Finset.strongInductionOn with
  | H S ih =>
    by_cases hn : S.Nonempty
    · let a := S.max' hn
      have ha : a ∈ S := S.max'_mem hn
      have hsmall : S.erase a ⊂ S := Finset.erase_ssubset ha
      have hi := ih (S.erase a) hsmall (fun b hb => hS b (Finset.mem_of_mem_erase hb))
      have hsub : S ⊆ Finset.Icc 3 a := by
        intro b hb
        exact Finset.mem_Icc.mpr ⟨hS b hb, Finset.le_max' S b hb⟩
      have hc := Finset.card_le_card hsub
      have hca := Finset.card_erase_add_one ha
      have hsum := Finset.sum_erase_add S (fun a : ℕ => a - 2) ha
      have hapos := hS a ha
      simp only [Nat.card_Icc] at hc
      nlinarith
    · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [this]

end WOWIITreeProof
