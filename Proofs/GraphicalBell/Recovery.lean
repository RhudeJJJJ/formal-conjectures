import Proofs.GraphicalBell.Partitions

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

lemma erased_block_not_mem {G : SimpleGraph V} {S : Finset V} {Q : Finset (Finset V)}
    (hQ : StableOn G S Q) {v : V} {U : Finset V} (hU : U ∈ Q) (hv : v ∈ U) :
    U.erase v ∉ Q := by
  intro hb
  obtain ⟨x, hx⟩ := (hQ.1 _ hb).1
  have he := stable_unique hQ hb hU hx (mem_of_mem_erase hx)
  rw [← he] at hv
  exact notMem_erase _ _ hv

lemma remove_erase_block {G : SimpleGraph V} {S : Finset V} {Q : Finset (Finset V)}
    (hQ : StableOn G S Q) {v : V} {U : Finset V} (hU : U ∈ Q) (hv : v ∈ U) :
    (removeVertex v Q).erase (U.erase v) = Q.erase U := by
  classical
  have hnot : ∀ C ∈ Q.erase U, v ∉ C := by
    intro C hc hvc
    obtain ⟨hne, hc⟩ := mem_erase.mp hc
    exact hne (stable_unique hQ hc hU hvc hv)
  ext C
  constructor
  · intro hc
    obtain ⟨hCB, hc⟩ := mem_erase.mp hc
    obtain ⟨_, hc⟩ := mem_erase.mp hc
    obtain ⟨D, hd, he⟩ := mem_image.mp hc
    by_cases hDU : D = U
    · subst D
      exact (hCB he.symm).elim
    · have hd' := mem_erase.mpr ⟨hDU, hd⟩
      have he' : D = C := by simpa [erase_eq_of_notMem (hnot D hd')] using he
      simpa [← he'] using hd'
  · intro hc
    have hCQ := mem_of_mem_erase hc
    have hCB : C ≠ U.erase v := by
      intro he
      exact erased_block_not_mem hQ hU hv (he ▸ hCQ)
    refine mem_erase.mpr ⟨hCB, ?_⟩
    refine mem_erase.mpr ⟨ne_of_mem_of_not_mem hCQ (stable_empty_not_mem hQ), ?_⟩
    exact mem_image.mpr ⟨C, hCQ, erase_eq_of_notMem (hnot C hc)⟩

lemma reconstruct {G : SimpleGraph V} {S : Finset V} {Q : Finset (Finset V)}
    (hQ : StableOn G S Q) {v : V} {U : Finset V} (hU : U ∈ Q) (hv : v ∈ U) :
    extendVertex v (removeVertex v Q) (U.erase v) = Q := by
  rw [extendVertex, remove_erase_block hQ hU hv, insert_erase hv, insert_erase hU]

lemma removed_block_eligible {G : SimpleGraph V} {S : Finset V} {Q : Finset (Finset V)}
    (hQ : StableOn G S Q) {v : V} {U : Finset V} (hU : U ∈ Q) (hv : v ∈ U) :
    (U.erase v = ∅ ∨ U.erase v ∈ removeVertex v Q) ∧
      ∀ w ∈ U.erase v, ¬ G.Adj v w := by
  constructor
  · by_cases hb : U.erase v = ∅
    · exact Or.inl hb
    · exact Or.inr (mem_erase.mpr ⟨hb, mem_image.mpr ⟨U, hU, rfl⟩⟩)
  · intro w hw
    exact (hQ.1 U hU).2 hv (mem_of_mem_erase hw) (Ne.symm (mem_erase.mp hw).1)

lemma extend_injective {G : SimpleGraph V} {S : Finset V} {P R : Finset (Finset V)}
    (hP : StableOn G S P) (hR : StableOn G S R) {v : V} (hv : v ∉ S)
    {B C : Finset V} (hB : B = ∅ ∨ B ∈ P) (hC : C = ∅ ∨ C ∈ R)
    (hfree : ∀ w ∈ B, ¬ G.Adj v w)
    (he : extendVertex v P B = extendVertex v R C) : P = R ∧ B = C := by
  have hPR : P = R := by
    have h := congrArg (removeVertex v) he
    rwa [remove_extend hP hv hB, remove_extend hR hv hC] at h
  have hQ := extend_stable hP hv hB hfree
  have hcQ : insert v C ∈ extendVertex v P B := by
    rw [he]
    exact mem_insert_self _ _
  have hh := stable_unique hQ (mem_insert_self _ _) hcQ (mem_insert_self _ _)
    (mem_insert_self _ _)
  have hbnot : v ∉ B := by
    rcases hB with rfl | hb
    · simp
    · exact fun h => hv (stable_subset hP hb h)
  have hcnot : v ∉ C := by
    rcases hC with rfl | hc
    · simp
    · exact fun h => hv (stable_subset hR hc h)
  have hBC := congrArg (fun U => U.erase v) hh
  exact ⟨hPR, by simpa [erase_insert hbnot, erase_insert hcnot] using hBC⟩

end GraphicalBellProof
