import Proofs.WOWII376354.MaximumCount
import Proofs.WOWII376354.HalfArithmetic

/-! Full original WOWII 376 certificate, using distance-sum minimizers. -/

open Finset SimpleGraph
namespace WOWIIMedian
open WrittenOnTheWallII.GraphConjecture376
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : SimpleGraph V) [DecidableRel T.Adj]

lemma card_split (D S : Finset V) : (D∩S).card+(D∩Sᶜ).card=D.card := by
  simpa only [sdiff_eq_inter_compl] using card_inter_add_card_sdiff D S

lemma two_medians_bound (hT : T.IsTree) (ho : 2<Fintype.card V)
    {D : Finset V} (hD : T.IsTotalDominating (D : Set V))
    {a b : V} (ha : a ∈ medians T) (hb : b ∈ medians T) (hne : a≠b) :
    (maximumDegreeIsolates T).card+2 ≤ D.card := by
  classical
  have hab := medians_adj T hT ha hb hne
  let A := side T a b
  let B := side T b a
  let I := maximumDegreeIsolates T
  have hB : B=Aᶜ := side_compl T hT hab
  have hsplitD : (D∩A).card+(D∩B).card=D.card := by rw [hB];exact card_split D A
  have hsplitI : (I∩A).card+(I∩B).card=I.card := by rw [hB];exact card_split I A
  have hbalanced : A.card=B.card := balanced_sides T hT hab ha hb
  have hn : Fintype.card V=2*A.card := by
    have hc := Finset.card_compl A
    rw [← hB] at hc
    have haPos : A.card≤Fintype.card V := card_le_univ A
    omega
  have hh : 2≤A.card := by omega
  have hδ := delta_ge_two T hT ho
  let t : ℕ := if a ∈ I then 1 else 0
  let u : ℕ := if b ∈ I then 1 else 0
  have ht : t≤1 := by dsimp [t];split_ifs <;> omega
  have hu : u≤1 := by dsimp [u];split_ifs <;> omega
  have htu : t+u≤1 := by
    by_cases hai : a ∈ I <;> by_cases hbi : b ∈ I
    · exact False.elim (isolates_independent T a hai b hbi hab)
    all_goals simp [t, u, hai, hbi]
  have hi := half_isolate_bound T hT hab
  have hj := half_isolate_bound T hT hab.symm
  have hsumA := side_cover_bound T hT hab hD
  have hsumB := side_cover_bound T hT hab.symm hD
  have hupper (S : Finset V) :
      (∑ d ∈ D∩S, internalDegree T S d)≤delta T*(D∩S).card := by
    calc
      _ ≤ ∑ _d ∈ D∩S, delta T := Finset.sum_le_sum (fun d _ =>
        (internal_le_degree T S d).trans (degree_le_delta T d))
      _ = _ := by simp [Nat.mul_comm]
  have hd := hsumA.trans (hupper A)
  have he := hsumB.trans (hupper B)
  by_contra hbad
  have hg : (D∩A).card+(D∩B).card≤(I∩A).card+(I∩B).card+1 := by omega
  have hIpos : I.Nonempty := by
    by_contra hnI
    have hzero : I.card=0 := by simp only [not_nonempty_iff_eq_empty.mp hnI,card_empty]
    have hDsmall : D.card≤1 := by omega
    let v := Classical.choice hT.connected.nonempty
    obtain ⟨d,hd,hvd⟩ := hD v
    obtain ⟨e,he,hde⟩ := hD d
    have hlarge : 1<D.card := Finset.one_lt_card.mpr ⟨d,hd,e,he,hde.ne⟩
    omega
  have hstrict := total_cover_strict T hD hIpos
  rw [hn,← hsplitD] at hstrict
  have hsat := fun hh' => saturated_half T hT hab hD hh hh'
  have hsat' := fun hh' => saturated_half T hT hab.symm hD
    (show 2≤B.card by omega) hh'
  exact balanced_count_impossible (delta T) A.card (I∩A).card (I∩B).card
    (D∩A).card (D∩B).card t u hδ hh ht hu htu
    hi (by simpa only [hbalanced] using hj) hd (by simpa only [hbalanced] using he)
    hg hstrict hsat (by simpa only [hbalanced] using hsat')

end WOWIIMedian

namespace WrittenOnTheWallII.GraphConjecture376
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem full_conjecture376 (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2<Fintype.card V) :
    (maximumDegreeIsolates T).card+(medians T).card≤T.totalDominationNumber := by
  obtain ⟨D,hD,hcard⟩ := WOWIICover.minimum_total_set T hT.connected (by omega)
  rw [← hcard]
  have hc := WOWIIMedian.medians_card_le_two T hT
  by_cases hm : (medians T).card≤1
  · exact (Nat.add_le_add_left hm _).trans (WOWIIMedian.basic_isolate_bound T hT hD)
  · have htwo : (medians T).card=2 := by omega
    obtain ⟨a,ha,b,hb,hne⟩ := Finset.one_lt_card.mp (show 1<(medians T).card by omega)
    rw [htwo]
    exact WOWIIMedian.two_medians_bound T hT horder hD ha hb hne
end WrittenOnTheWallII.GraphConjecture376
