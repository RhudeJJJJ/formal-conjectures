import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Partition.Finpartition
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

def StableOn (G : SimpleGraph V) (S : Finset V) (P : Finset (Finset V)) : Prop :=
  (∀ B ∈ P, B.Nonempty ∧ G.IsIndepSet (B : Set V)) ∧
  (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧ P.biUnion id = S

abbrev Parts (G : SimpleGraph V) (S : Finset V) := {P : Finset (Finset V) // StableOn G S P}
abbrev Graded (G : SimpleGraph V) (S : Finset V) (k : ℕ) :=
  {P : Parts G S // P.val.card = k}

instance finiteParts (G : SimpleGraph V) (S : Finset V) : Finite (Parts G S) := by
  classical
  let f : Parts G S → S.powerset.powerset := fun P =>
    ⟨P.val, mem_powerset.mpr (by
      intro B hb
      exact mem_powerset.mpr (by
        intro x hx
        rw [← P.property.2.2]
        exact mem_biUnion.mpr ⟨B, hb, hx⟩))⟩
  apply Finite.of_injective f
  intro P Q h
  apply Subtype.ext
  exact congrArg (fun t : S.powerset.powerset => t.val) h

noncomputable instance partsFintype (G : SimpleGraph V) (S : Finset V) :
    Fintype (Parts G S) := Fintype.ofFinite _

noncomputable def count (G : SimpleGraph V) (S : Finset V) (k : ℕ) : ℕ :=
  Nat.card (Graded G S k)

def removeVertex (v : V) (P : Finset (Finset V)) : Finset (Finset V) :=
  (P.image (fun B => B.erase v)).erase ∅

def extendVertex (v : V) (P : Finset (Finset V)) (B : Finset V) : Finset (Finset V) :=
  insert (insert v B) (P.erase B)

lemma stable_subset {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) {B : Finset V} (hB : B ∈ P) : B ⊆ S := by
  intro x hx
  rw [← hP.2.2]
  exact mem_biUnion.mpr ⟨B, hB, hx⟩

lemma stable_empty_not_mem {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) : ∅ ∉ P := by
  intro h
  exact not_nonempty_empty (hP.1 ∅ h).1

lemma stable_unique {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) {B C : Finset V} (hB : B ∈ P) (hC : C ∈ P)
    {x : V} (hx : x ∈ B) (hy : x ∈ C) : B = C := by
  by_contra hn
  exact (disjoint_left.mp (hP.2.1 B hB C hC hn)) hx hy

lemma remove_stable {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) (v : V) : StableOn G (S.erase v) (removeVertex v P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨hne, hb⟩ := mem_erase.mp hB
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hb
    exact ⟨nonempty_iff_ne_empty.mpr hne, (hP.1 C hC).2.mono (by
      intro x hx
      exact mem_of_mem_erase hx)⟩
  · intro B hB C hC hne
    obtain ⟨_, hb⟩ := mem_erase.mp hB
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hb
    obtain ⟨_, hc⟩ := mem_erase.mp hC
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hc
    exact (hP.2.1 D hD E hE (fun h => hne (congrArg (fun B => B.erase v) h))).mono
      (erase_subset _ _) (erase_subset _ _)
  · ext x
    simp only [removeVertex, mem_biUnion, mem_erase, ne_eq, mem_image]
    constructor
    · rintro ⟨B, ⟨_, C, hC, rfl⟩, hx⟩
      exact ⟨(mem_erase.mp hx).1, stable_subset hP hC (mem_of_mem_erase hx)⟩
    · rintro ⟨hxv, hx⟩
      have : x ∈ P.biUnion id := by rwa [hP.2.2]
      obtain ⟨B, hB, hxb⟩ := mem_biUnion.mp this
      refine ⟨B.erase v, ⟨?_, B, hB, rfl⟩, ?_⟩
      · exact nonempty_iff_ne_empty.mp ⟨x, mem_erase.mpr ⟨hxv, hxb⟩⟩
      · exact mem_erase.mpr ⟨hxv, hxb⟩

lemma remove_extend {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) {v : V} (hv : v ∉ S) {B : Finset V}
    (hB : B = ∅ ∨ B ∈ P) : removeVertex v (extendVertex v P B) = P := by
  classical
  have hnot : ∀ C ∈ P, v ∉ C := fun C hc hvc => hv (stable_subset hP hc hvc)
  have hbnot : v ∉ B := by rcases hB with rfl | hb; simp; exact hnot B hb
  ext C
  simp only [removeVertex, extendVertex, mem_erase, mem_image, mem_insert, exists_eq_or_imp]
  constructor
  · rintro ⟨hne, h | ⟨D, ⟨hDB, hD⟩, hDC⟩⟩
    · have hBC : B = C := by simpa [erase_insert hbnot] using h
      subst C
      simpa [erase_insert hbnot] using hB.resolve_left (by simpa [erase_insert hbnot] using hne)
    · have hDC' : D = C := by simpa [erase_eq_of_notMem (hnot D hD)] using hDC
      simpa [← hDC'] using hD
  · intro hc
    refine ⟨ne_of_mem_of_not_mem hc (stable_empty_not_mem hP), ?_⟩
    by_cases hCB : C = B
    · left
      subst C
      exact erase_insert hbnot
    · right
      exact ⟨C, ⟨hCB, hc⟩, erase_eq_of_notMem (hnot C hc)⟩

lemma extend_stable {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) {v : V} (hv : v ∉ S) {B : Finset V}
    (hB : B = ∅ ∨ B ∈ P) (hfree : ∀ w ∈ B, ¬ G.Adj v w) :
    StableOn G (insert v S) (extendVertex v P B) := by
  classical
  have hnot : ∀ C ∈ P, v ∉ C := fun C hc hvc => hv (stable_subset hP hc hvc)
  have hBind : G.IsIndepSet (B : Set V) := by
    rcases hB with rfl | hb
    · intro x hx
      simp at hx
    · exact (hP.1 B hb).2
  refine ⟨?_, ?_, ?_⟩
  · intro C hc
    rcases mem_insert.mp hc with rfl | hc
    · refine ⟨insert_nonempty _ _, ?_⟩
      intro x hx y hy hxy
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact (hxy rfl).elim
        · exact hfree y hy
      · rcases hy with rfl | hy
        · exact fun h => hfree x hx (G.symm.symm _ _ h)
        · exact hBind hx hy hxy
    · exact hP.1 C (mem_of_mem_erase hc)
  · intro C hc D hd hCD
    rcases mem_insert.mp hc with rfl | hc
    · have hd : D ∈ P.erase B := (mem_insert.mp hd).resolve_left (Ne.symm hCD)
      obtain ⟨hDB, hd⟩ := mem_erase.mp hd
      refine disjoint_left.mpr ?_
      intro x hx hxd
      rcases mem_insert.mp hx with hx | hx
      · exact hnot D hd (hx ▸ hxd)
      · rcases hB with rfl | hb
        · simp at hx
        · exact disjoint_left.mp (hP.2.1 B hb D hd (Ne.symm hDB)) hx hxd
    · rcases mem_insert.mp hd with rfl | hd
      · obtain ⟨hCB, hc⟩ := mem_erase.mp hc
        refine disjoint_left.mpr ?_
        intro x hxc hx
        rcases mem_insert.mp hx with hx | hx
        · exact hnot C hc (hx ▸ hxc)
        · rcases hB with rfl | hb
          · simp at hx
          · exact disjoint_left.mp (hP.2.1 C hc B hb hCB) hxc hx
      · exact hP.2.1 C (mem_of_mem_erase hc) D (mem_of_mem_erase hd) hCD
  · ext x
    simp only [extendVertex, mem_biUnion, mem_insert, mem_erase, ne_eq, exists_eq_or_imp, id_eq]
    constructor
    · rintro (hx | ⟨C, ⟨_, hc⟩, hx⟩)
      · rcases hx with rfl | hx
        · exact Or.inl rfl
        · right
          rcases hB with rfl | hb
          · simp at hx
          · exact stable_subset hP hb hx
      · exact Or.inr (stable_subset hP hc hx)
    · rintro (rfl | hx)
      · exact Or.inl (Or.inl rfl)
      · obtain ⟨C, hc, hxc⟩ := mem_biUnion.mp (show x ∈ P.biUnion id by rwa [hP.2.2])
        by_cases hCB : C = B
        · exact Or.inl (Or.inr (hCB ▸ hxc))
        · exact Or.inr ⟨C, ⟨hCB, hc⟩, hxc⟩

lemma extend_card {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) {v : V} (hv : v ∉ S) {B : Finset V}
    (hB : B = ∅ ∨ B ∈ P) :
    (extendVertex v P B).card = P.card + if B = ∅ then 1 else 0 := by
  have hn : insert v B ∉ P.erase B := by
    intro hc
    exact hv (stable_subset hP (mem_of_mem_erase hc) (mem_insert_self _ _))
  rw [extendVertex, card_insert_of_notMem hn]
  rcases hB with rfl | hb
  · simp [stable_empty_not_mem hP]
  · rw [card_erase_of_mem hb, if_neg (ne_of_mem_of_not_mem hb (stable_empty_not_mem hP))]
    have := card_pos.mpr ⟨B, hb⟩
    omega

end GraphicalBellProof
