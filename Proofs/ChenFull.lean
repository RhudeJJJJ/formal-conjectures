import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import FormalConjectures.Paper.ChenTotalDomination

/-!
# Complete certificate for Chen Conjecture 4

Construct local total-neighbor covers for complementary induced parts and combine them.
The length-two-path construction also proves the ordinary-complement bound.
The exact target uses the unchanged definitions imported from the statement PR.
-/

set_option Elab.async false

namespace ChenCertificate
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

def Covers (G : SimpleGraph V) (X W : Finset V) : Prop :=
  ∀ v ∈ W, ∃ w ∈ X, G.Adj v w

theorem cover_by_choices (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    (W : Finset V) : ∃ X, Covers G X W ∧ X.card ≤ W.card := by
  classical
  choose f hf using hG
  refine ⟨W.image f, ?_, card_image_le⟩
  intro v hv
  exact ⟨f v, mem_image.mpr ⟨v, hv, rfl⟩, hf v⟩

theorem extend_pair (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    (W A : Finset V) (v a : V)
    (h : ∀ z ∈ W, z ∉ A → G.Adj z v ∨ G.Adj z a) :
    ∃ X, Covers G X W ∧ X.card ≤ A.card + 2 := by
  classical
  obtain ⟨Y, hY, hc⟩ := cover_by_choices G hG A
  refine ⟨{v,a} ∪ Y, ?_, ?_⟩
  · intro z hz
    by_cases hza : z ∈ A
    · obtain ⟨w, hw, hzw⟩ := hY z hza
      exact ⟨w, mem_union_right _ hw, hzw⟩
    · rcases h z hz hza with hv | ha
      · exact ⟨v, mem_union_left _ (by simp), hv⟩
      · exact ⟨a, mem_union_left _ (by simp), ha⟩
  · have hpair : ({v,a} : Finset V).card ≤ 2 := by
      exact (card_insert_le v {a}).trans (by simp)
    exact (card_union_le _ _).trans (by omega)

theorem local_cover (G H : SimpleGraph V)
    (hG : ∀ v, ∃ w, G.Adj v w) (hH : ∀ v, ∃ w, H.Adj v w)
    (W : Finset V)
    (hcomp : ∀ v ∈ W, ∀ w ∈ W, v ≠ w → (H.Adj v w ↔ ¬ G.Adj v w)) :
    ∃ X Y, Covers G X W ∧ Covers H Y W ∧ X.card + Y.card ≤ W.card + 2 := by
  classical
  by_cases hsmall : W.card ≤ 1
  · obtain ⟨X, hX, hcX⟩ := cover_by_choices G hG W
    obtain ⟨Y, hY, hcY⟩ := cover_by_choices H hH W
    exact ⟨X,Y,hX,hY,by omega⟩
  have hnonempty : W.Nonempty := card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hnonempty
  have hex : ∃ w ∈ W, w ≠ v := by
    by_contra! h
    have : W ⊆ {v} := by intro x hx; simp [h x hx]
    have := card_le_card this
    simp only [card_singleton] at this
    omega
  obtain ⟨w, hw, hwv⟩ := hex
  by_cases hGi : ∃ a ∈ W, G.Adj v a
  · by_cases hHi : ∃ b ∈ W, H.Adj v b
    · obtain ⟨a, ha, hva⟩ := hGi
      obtain ⟨b, hb, hvb⟩ := hHi
      let B := W.filter fun z => z ≠ v ∧ ¬ G.Adj v z
      let C := W.filter fun z => z ≠ v ∧ ¬ H.Adj v z
      have hB : b ∈ B := by
        simp only [B, mem_filter]
        exact ⟨hb, Ne.symm hvb.ne, (hcomp v hv b hb hvb.ne).mp hvb⟩
      have hC : a ∈ C := by
        simp only [C, mem_filter]
        refine ⟨ha, Ne.symm hva.ne, ?_⟩
        intro hvaH
        exact (hcomp v hv a ha hva.ne).mp hvaH hva
      have hBC : B.card + C.card + 1 = W.card := by
        have hd : Disjoint B C := by
          apply Finset.disjoint_left.mpr
          intro z hzB hzC
          simp only [B, C, mem_filter] at hzB hzC
          exact hzC.2.2 ((hcomp v hv z hzB.1 (Ne.symm hzB.2.1)).mpr hzB.2.2)
        have hu : B ∪ C = W.erase v := by
          ext z
          simp only [mem_union, B, C, mem_filter, mem_erase]
          constructor
          · rintro (⟨hz, hzv, _⟩ | ⟨hz, hzv, _⟩) <;> exact ⟨hzv,hz⟩
          · rintro ⟨hzv,hz⟩
            by_cases hgz : G.Adj v z
            · right
              exact ⟨hz,hzv,fun hhz => (hcomp v hv z hz (Ne.symm hzv)).mp hhz hgz⟩
            · exact Or.inl ⟨hz,hzv,hgz⟩
        have := card_union_of_disjoint hd
        rw [hu, card_erase_of_mem hv] at this
        omega
      have baseG : ∀ z ∈ W, z ∉ B → G.Adj z v ∨ G.Adj z a := by
        intro z hz hzb
        by_cases hzv : z = v
        · subst z; exact Or.inr hva
        · left
          refine (show G.Adj v z from ?_).symm
          by_contra hn
          exact hzb (by simp [B, hz, hzv, hn])
      have baseH : ∀ z ∈ W, z ∉ C → H.Adj z v ∨ H.Adj z b := by
        intro z hz hzc
        by_cases hzv : z = v
        · subst z; exact Or.inr hvb
        · left
          refine (show H.Adj v z from ?_).symm
          by_contra hn
          exact hzc (by simp [C, hz, hzv, hn])
      by_cases hab : G.Adj a b
      · obtain ⟨X,hX,hcX⟩ := extend_pair G hG W (B.erase b) v a (by
          intro z hz hzerase
          by_cases hzb : z = b
          · subst z; exact Or.inr hab.symm
          · exact baseG z hz (fun hzB => hzerase (mem_erase.mpr ⟨hzb,hzB⟩)))
        obtain ⟨Y,hY,hcY⟩ := extend_pair H hH W C v b baseH
        have he := card_erase_of_mem hB
        have hpos := card_pos.mpr (show B.Nonempty from ⟨b,hB⟩)
        exact ⟨X,Y,hX,hY,by omega⟩
      · have habne : a ≠ b := by
          intro he
          exact (hcomp v hv b hb hvb.ne).mp hvb (he ▸ hva)
        have hab' : H.Adj a b := (hcomp a ha b hb habne).mpr hab
        obtain ⟨X,hX,hcX⟩ := extend_pair G hG W B v a baseG
        obtain ⟨Y,hY,hcY⟩ := extend_pair H hH W (C.erase a) v b (by
          intro z hz hzerase
          by_cases hza : z = a
          · subst z; exact Or.inr hab'
          · exact baseH z hz (fun hzC => hzerase (mem_erase.mpr ⟨hza,hzC⟩)))
        have he := card_erase_of_mem hC
        have hpos := card_pos.mpr (show C.Nonempty from ⟨a,hC⟩)
        exact ⟨X,Y,hX,hY,by omega⟩
    · push Not at hHi
      obtain ⟨Y,hY,hcY⟩ := cover_by_choices H hH W
      have hX : Covers G {v,w} W := by
        intro z hz
        by_cases hzv : z = v
        · subst z
          exact ⟨w,by simp,by
            by_contra hn
            exact hHi w hw ((hcomp v hv w hw (Ne.symm hwv)).mpr hn)⟩
        · refine ⟨v,by simp, (show G.Adj v z from ?_).symm⟩
          by_contra hn
          exact hHi z hz ((hcomp v hv z hz (Ne.symm hzv)).mpr hn)
      have hcX : ({v,w}:Finset V).card ≤ 2 := (card_insert_le _ _).trans (by simp)
      exact ⟨{v,w},Y,hX,hY,by omega⟩
  · push Not at hGi
    obtain ⟨X,hX,hcX⟩ := cover_by_choices G hG W
    have hY : Covers H {v,w} W := by
      intro z hz
      by_cases hzv : z = v
      · subst z
        exact ⟨w,by simp,(hcomp v hv w hw (Ne.symm hwv)).mpr (hGi w hw)⟩
      · exact ⟨v,by simp,((hcomp v hv z hz (Ne.symm hzv)).mpr (hGi z hz)).symm⟩
    have hcY : ({v,w}:Finset V).card ≤ 2 := (card_insert_le _ _).trans (by simp)
    exact ⟨X,{v,w},hX,hY,by omega⟩

variable [Fintype V]

theorem partition_bound (G H : SimpleGraph V)
    (hG : ∀ v, ∃ w, G.Adj v w) (hH : ∀ v, ∃ w, H.Adj v w)
    (c : V → ℕ)
    (hcomp : ∀ v w, c v = c w → v ≠ w → (H.Adj v w ↔ ¬ G.Adj v w)) :
    G.totalDominationNumber + H.totalDominationNumber ≤
      Fintype.card V + 2 * (univ.image c).card := by
  classical
  let K := univ.image c
  let W := fun d => univ.filter fun v => c v = d
  have hlocal : ∀ d, ∃ X Y, Covers G X (W d) ∧ Covers H Y (W d) ∧
      X.card + Y.card ≤ (W d).card + 2 := by
    intro d
    apply local_cover G H hG hH (W d)
    intro v hv w hw hvw
    exact hcomp v w ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm) hvw
  choose X Y hX hY hcard using hlocal
  let DX := K.biUnion X
  let DY := K.biUnion Y
  have hdX : G.IsTotalDominating (DX : Set V) := by
    intro v
    obtain ⟨w, hw, hvw⟩ := hX (c v) v (by simp [W])
    exact ⟨w, mem_biUnion.mpr ⟨c v, mem_image.mpr ⟨v,mem_univ v,rfl⟩,hw⟩,hvw⟩
  have hdY : H.IsTotalDominating (DY : Set V) := by
    intro v
    obtain ⟨w, hw, hvw⟩ := hY (c v) v (by simp [W])
    exact ⟨w, mem_biUnion.mpr ⟨c v, mem_image.mpr ⟨v,mem_univ v,rfl⟩,hw⟩,hvw⟩
  have hnX : G.totalDominationNumber ≤ DX.card :=
    Nat.sInf_le ⟨DX,⟨hdX,rfl⟩⟩
  have hnY : H.totalDominationNumber ≤ DY.card :=
    Nat.sInf_le ⟨DY,⟨hdY,rfl⟩⟩
  have hDX : DX.card ≤ ∑ d ∈ K, (X d).card := card_biUnion_le
  have hDY : DY.card ≤ ∑ d ∈ K, (Y d).card := card_biUnion_le
  have hsum : (∑ d ∈ K, (X d).card) + (∑ d ∈ K, (Y d).card) ≤
      (∑ d ∈ K, (W d).card) + 2 * K.card := by
    have h := sum_le_sum (fun d (_ : d ∈ K) => hcard d)
    simpa [sum_add_distrib, mul_comm] using h
  have hW : ∑ d ∈ K, (W d).card = Fintype.card V := by
    simpa only [W, K, card_univ] using (card_eq_sum_card_image c (univ : Finset V)).symm
  rw [hW] at hsum
  exact (Nat.add_le_add hnX hnY).trans ((Nat.add_le_add hDX hDY).trans hsum)

#print axioms local_cover
#print axioms partition_bound
end ChenCertificate

namespace Chen.DeltaComplement
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem full_conjecture4 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ v, ∃ w, G.Adj v w)
    (hDelta : ∀ v, ∃ w, (deltaComplement G).Adj v w) :
    G.totalDominationNumber + (deltaComplement G).totalDominationNumber ≤
      Fintype.card V + 2 * degreeClassCount G := by
  apply ChenCertificate.partition_bound G (deltaComplement G) hG hDelta (fun v => G.degree v)
  intro v w hd hn
  simp [deltaComplement, hd, hn]

#print axioms full_conjecture4
end Chen.DeltaComplement
