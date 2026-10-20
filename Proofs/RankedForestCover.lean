import Proofs.StrictHallForest

/-! A simultaneous vertex cover and edge cover in a ranked forest.
The sum of their cardinalities is at most the number of vertices. -/
namespace StrictHallForest
open Finset SimpleGraph
variable {W : Type*} [DecidableEq W]

lemma exists_covers_on (G : SimpleGraph W) (rank : W → ℕ)
    (hne : ∀ u v, G.Adj u v → rank u ≠ rank v)
    (hunique : ∀ u v w, G.Adj u v → G.Adj u w →
      rank v < rank u → rank w < rank u → v = w) (S : Finset W) :
    ∃ C : Finset W, ∃ D : Finset (W × W),
      C ⊆ S ∧
      (∀ e ∈ D, e.1 ∈ S ∧ e.2 ∈ S ∧ G.Adj e.1 e.2) ∧
      (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → u ∈ C ∨ v ∈ C) ∧
      (∀ u ∈ S, (∃ v ∈ S, G.Adj u v) → ∃ e ∈ D, u = e.1 ∨ u = e.2) ∧
      C.card + D.card ≤ S.card := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hS : S.Nonempty
  · obtain ⟨u, hu, hmax⟩ := exists_max_image S rank hS
    have huunique : ∀ v ∈ S, ∀ w ∈ S, G.Adj u v → G.Adj u w → v = w := by
      intro v hv w hw huv huw
      have := hmax v hv
      have := hmax w hw
      have := hne u v huv
      have := hne u w huw
      exact hunique u v w huv huw (by omega) (by omega)
    by_cases hnadj : ∃ v ∈ S, G.Adj u v
    · obtain ⟨v, hv, huv⟩ := hnadj
      let L := S.filter (fun w => G.Adj w v ∧ ∀ x ∈ S, G.Adj w x → x = v)
      have huL : u ∈ L := by
        exact mem_filter.mpr ⟨hu, huv, fun x hx hux => huunique x hx v hv hux huv⟩
      have hvL : v ∉ L := by simp [L]
      let K := insert v L
      let T := S \ K
      have hKS : K ⊆ S := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact hv
        · exact (mem_filter.mp hw).1
      have hTs : T ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, ?_⟩
        intro he
        have : v ∈ T := he.symm ▸ hv
        exact (mem_sdiff.mp this).2 (mem_insert_self v L)
      obtain ⟨C, D, hCS, hDE, hCE, hDC, hcard⟩ := ih T hTs
      let C' := insert v C
      let D' := D ∪ L.image (fun w => (w, v))
      have hremain (w : W) (hw : w ∈ T) (hn : ∃ x ∈ S, G.Adj w x) :
          ∃ x ∈ T, G.Adj w x := by
        have hwS := (mem_sdiff.mp hw).1
        have hwK := (mem_sdiff.mp hw).2
        have hwv : w ≠ v := fun he => hwK (he ▸ mem_insert_self v L)
        have hwL : w ∉ L := fun he => hwK (mem_insert_of_mem he)
        obtain ⟨x, hx, hwx⟩ := hn
        by_cases hxv : x = v
        · have hex : ∃ y ∈ S, G.Adj w y ∧ y ≠ v := by
            by_contra! hh
            exact hwL (mem_filter.mpr ⟨hwS, hxv ▸ hwx, hh⟩)
          obtain ⟨y, hy, hwy, hyv⟩ := hex
          refine ⟨y, mem_sdiff.mpr ⟨hy, ?_⟩, hwy⟩
          intro hyK
          rcases mem_insert.mp hyK with he | hyL
          · exact hyv he
          · have := (mem_filter.mp hyL).2.2 w hwS hwy.symm
            exact hwv this
        · refine ⟨x, mem_sdiff.mpr ⟨hx, ?_⟩, hwx⟩
          intro hxK
          rcases mem_insert.mp hxK with he | hxL
          · exact hxv he
          · exact hwv ((mem_filter.mp hxL).2.2 w hwS hwx.symm)
      refine ⟨C', D', ?_, ?_, ?_, ?_, ?_⟩
      · intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact hv
        · exact (mem_sdiff.mp (hCS hw)).1
      · intro e he
        rcases mem_union.mp he with he | he
        · obtain ⟨h1, h2, ha⟩ := hDE e he
          exact ⟨(mem_sdiff.mp h1).1, (mem_sdiff.mp h2).1, ha⟩
        · obtain ⟨w, hw, rfl⟩ := mem_image.mp he
          exact ⟨(mem_filter.mp hw).1, hv, (mem_filter.mp hw).2.1⟩
      · intro a ha b hb hab
        by_cases hav : a = v
        · exact Or.inl (hav ▸ mem_insert_self v C)
        by_cases hbv : b = v
        · exact Or.inr (hbv ▸ mem_insert_self v C)
        have hat : a ∈ T := by
          refine mem_sdiff.mpr ⟨ha, ?_⟩
          intro haK
          rcases mem_insert.mp haK with h | haL
          · exact hav h
          · exact hbv ((mem_filter.mp haL).2.2 b hb hab)
        have hbt : b ∈ T := by
          refine mem_sdiff.mpr ⟨hb, ?_⟩
          intro hbK
          rcases mem_insert.mp hbK with h | hbL
          · exact hbv h
          · exact hav ((mem_filter.mp hbL).2.2 a ha hab.symm)
        exact (hCE a hat b hbt hab).imp (mem_insert_of_mem) (mem_insert_of_mem)
      · intro w hw hn
        by_cases hwv : w = v
        · refine ⟨(u, v), mem_union_right _ (mem_image.mpr ⟨u, huL, rfl⟩), Or.inr hwv⟩
        by_cases hwL : w ∈ L
        · exact ⟨(w, v), mem_union_right _ (mem_image.mpr ⟨w, hwL, rfl⟩), Or.inl rfl⟩
        have hwt : w ∈ T := mem_sdiff.mpr ⟨hw, by simpa [K] using And.intro hwv hwL⟩
        obtain ⟨e, he, hwe⟩ := hDC w hwt (hremain w hwt hn)
        exact ⟨e, mem_union_left _ he, hwe⟩
      · have hc' : C'.card ≤ C.card + 1 := card_insert_le _ _
        have hd' : D'.card ≤ D.card + L.card := by
          exact (card_union_le _ _).trans (Nat.add_le_add_left (card_image_le) _)
        have hk : K.card = L.card + 1 := card_insert_of_notMem hvL
        have htk := card_sdiff_add_card_eq_card hKS
        change T.card + K.card = S.card at htk
        omega
    · have hu0 : ∀ v ∈ S, ¬ G.Adj u v := by simpa using hnadj
      obtain ⟨C, D, hCS, hDE, hCE, hDC, hcard⟩ := ih (S.erase u) (erase_ssubset hu)
      refine ⟨C, D, ?_, ?_, ?_, ?_, ?_⟩
      · exact hCS.trans (erase_subset _ _)
      · intro e he
        obtain ⟨h1, h2, ha⟩ := hDE e he
        exact ⟨(mem_erase.mp h1).2, (mem_erase.mp h2).2, ha⟩
      · intro a ha b hb hab
        have hau : a ≠ u := by rintro rfl; exact hu0 b hb hab
        have hbu : b ≠ u := by rintro rfl; exact hu0 a ha hab.symm
        exact hCE a (mem_erase.mpr ⟨hau, ha⟩) b (mem_erase.mpr ⟨hbu, hb⟩) hab
      · intro a ha hn
        obtain ⟨b, hb, hab⟩ := hn
        have hau : a ≠ u := by rintro rfl; exact hu0 b hb hab
        have hbu : b ≠ u := by rintro rfl; exact hu0 a ha hab.symm
        exact hDC a (mem_erase.mpr ⟨hau, ha⟩) ⟨b, mem_erase.mpr ⟨hbu, hb⟩, hab⟩
      · exact hcard.trans (card_le_card (erase_subset _ _))
  · refine ⟨∅, ∅, empty_subset _, ?_, ?_, ?_, by simp⟩
    · simp
    · intro u hu
      exact False.elim (hS ⟨u, hu⟩)
    · intro u hu
      exact False.elim (hS ⟨u, hu⟩)

/-- Strict Hall and nonempty ground incidences give simultaneous transversals
of the family and its ground set with combined size at most the ground set. -/
theorem exists_incidence_cover {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Finset W) (W₀ : Finset W)
    (hHall : ∀ S : Finset I, S.Nonempty → S.card + 1 ≤ (S.biUnion E).card)
    (hEW : ∀ i, E i ⊆ W₀) (hcover : ∀ w ∈ W₀, ∃ i, w ∈ E i) :
    ∃ C : Finset W, ∃ J : Finset I,
      C ⊆ W₀ ∧ (∀ i, ∃ w ∈ C, w ∈ E i) ∧
      (∀ w ∈ W₀, ∃ i ∈ J, w ∈ E i) ∧ C.card + J.card ≤ W₀.card := by
  classical
  obtain ⟨f, p, rank, hf, hfm, hpm, hr⟩ := exists_ranked_selection E hHall
  let H := selectionGraph f p (fun i => (hpm i).2)
  let R := vertexRank f rank
  have hd (i : I) : R (p i) < R (f i) := vertexRank_parent f p rank hf hr i
  have hne : ∀ u v, H.Adj u v → R u ≠ R v := by
    rintro u v ⟨i, h | h⟩ <;> rcases h with ⟨rfl, rfl⟩
    · exact (hd i).ne'
    · exact (hd i).ne
  have huniq : ∀ u v w, H.Adj u v → H.Adj u w →
      R v < R u → R w < R u → v = w := by
    intro u v w huv huw hv hw
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
  have hinc : ∀ u v, H.Adj u v → ∃ i, u ∈ E i ∧ v ∈ E i := by
    rintro u v ⟨i, h | h⟩ <;> rcases h with ⟨rfl, rfl⟩
    · exact ⟨i, hfm i, (hpm i).1⟩
    · exact ⟨i, (hpm i).1, hfm i⟩
  have hends : ∀ u v, H.Adj u v → u ∈ W₀ ∧ v ∈ W₀ := by
    intro u v huv
    obtain ⟨i, hu, hv⟩ := hinc u v huv
    exact ⟨hEW i hu, hEW i hv⟩
  let S := W₀.filter (fun w => ∃ v, H.Adj w v)
  have hSS : S ⊆ W₀ := filter_subset _ _
  have hadjS : ∀ u v, H.Adj u v → u ∈ S ∧ v ∈ S := by
    intro u v huv
    obtain ⟨hu, hv⟩ := hends u v huv
    exact ⟨mem_filter.mpr ⟨hu, v, huv⟩, mem_filter.mpr ⟨hv, u, huv.symm⟩⟩
  obtain ⟨C, D, hCS, hDE, hCE, hDC, hcard⟩ := exists_covers_on H R hne huniq S
  have hlabel : ∀ e : {e // e ∈ D}, ∃ i, e.val.1 ∈ E i ∧ e.val.2 ∈ E i := by
    intro e
    exact hinc _ _ (hDE e.val e.property).2.2
  choose label hlabel using hlabel
  let J₁ := D.attach.image label
  let U := W₀ \ S
  have hextra : ∀ w : {w // w ∈ U}, ∃ i, w.val ∈ E i := by
    intro w
    exact hcover w.val (mem_sdiff.mp w.property).1
  choose extra hextra using hextra
  let J₂ := U.attach.image extra
  refine ⟨C, J₁ ∪ J₂, hCS.trans hSS, ?_, ?_, ?_⟩
  · intro i
    have ha : H.Adj (f i) (p i) := ⟨i, Or.inl ⟨rfl, rfl⟩⟩
    have hs := hadjS _ _ ha
    rcases hCE _ hs.1 _ hs.2 ha with h | h
    · exact ⟨f i, h, hfm i⟩
    · exact ⟨p i, h, (hpm i).1⟩
  · intro w hw
    by_cases hs : w ∈ S
    · obtain ⟨v, hwv⟩ := (mem_filter.mp hs).2
      obtain ⟨e, he, hwe⟩ := hDC w hs ⟨v, (hadjS _ _ hwv).2, hwv⟩
      let e' : {e // e ∈ D} := ⟨e, he⟩
      refine ⟨label e', mem_union_left _ (mem_image.mpr ⟨e', mem_attach _ _, rfl⟩), ?_⟩
      rcases hwe with rfl | rfl
      · exact (hlabel e').1
      · exact (hlabel e').2
    · let w' : {w // w ∈ U} := ⟨w, mem_sdiff.mpr ⟨hw, hs⟩⟩
      exact ⟨extra w', mem_union_right _ (mem_image.mpr ⟨w', mem_attach _ _, rfl⟩), hextra w'⟩
  · have hj₁ : J₁.card ≤ D.card := by
      exact (card_image_le).trans_eq (card_attach)
    have hj₂ : J₂.card ≤ U.card := by
      exact (card_image_le).trans_eq (card_attach)
    have hju := card_union_le J₁ J₂
    have hsu := card_sdiff_add_card_eq_card hSS
    change U.card + S.card = W₀.card at hsu
    omega

end StrictHallForest
