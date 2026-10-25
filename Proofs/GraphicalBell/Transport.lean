import Proofs.GraphicalBell.Partitions

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def mapParts (f : V → W) (P : Finset (Finset V)) : Finset (Finset W) :=
  P.image (fun B => B.image f)

noncomputable def pullParts (f : V → W) (S : Finset V) (Q : Finset (Finset W)) :
    Finset (Finset V) := by
  classical
  exact Q.image (fun C => S.filter (fun x => f x ∈ C))

lemma mapFinset_injective {f : V → W} (hf : Function.Injective f) :
    Function.Injective (fun B : Finset V => B.image f) := by
  intro B C h
  change B.image f = C.image f at h
  ext x
  constructor
  · intro hx
    have hfx : f x ∈ C.image f := h ▸ mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := mem_image.mp hfx
    exact hf he ▸ hy
  · intro hx
    have hfx : f x ∈ B.image f := h.symm ▸ mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := mem_image.mp hfx
    exact hf he ▸ hy

lemma mapParts_card {f : V → W} (hf : Function.Injective f) (P : Finset (Finset V)) :
    (mapParts f P).card = P.card := card_image_of_injective P (mapFinset_injective hf)

lemma map_stable {f : V → W} (hf : Function.Injective f) {G : SimpleGraph V}
    {H : SimpleGraph W} (hr : ∀ x y, G.Adj x y ↔ H.Adj (f x) (f y))
    {S : Finset V} {P : Finset (Finset V)} (hP : StableOn G S P) :
    StableOn H (S.image f) (mapParts f P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B hb
    obtain ⟨C, hc, rfl⟩ := mem_image.mp hb
    obtain ⟨x, hx⟩ := (hP.1 C hc).1
    refine ⟨⟨f x, mem_image.mpr ⟨x, hx, rfl⟩⟩, ?_⟩
    intro u hu v hv huv
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hv
    intro hadj
    exact (hP.1 C hc).2 ha hb (fun h => huv (congrArg f h)) ((hr a b).mpr hadj)
  · intro B hb C hc hBC
    obtain ⟨D, hd, rfl⟩ := mem_image.mp hb
    obtain ⟨E, he, rfl⟩ := mem_image.mp hc
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u, hu, hux⟩ := mem_image.mp hx
    obtain ⟨v, hv, hvx⟩ := mem_image.mp hy
    have huv := hf (hux.trans hvx.symm)
    exact Finset.disjoint_left.mp (hP.2.1 D hd E he (fun h => hBC (congrArg (fun B => B.image f) h)))
      hu (huv.symm ▸ hv)
  · ext x
    constructor
    · intro hx
      obtain ⟨B, hb, hxb⟩ := mem_biUnion.mp hx
      obtain ⟨C, hc, rfl⟩ := mem_image.mp hb
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hxb
      exact mem_image.mpr ⟨y, stable_subset hP hc hy, rfl⟩
    · intro hx
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      obtain ⟨B, hb, hab⟩ := mem_biUnion.mp (show a ∈ P.biUnion id by rwa [hP.2.2])
      exact mem_biUnion.mpr ⟨B.image f, mem_image.mpr ⟨B, hb, rfl⟩,
        mem_image.mpr ⟨a, hab, rfl⟩⟩

lemma pull_stable {f : V → W} (hf : Function.Injective f) {G : SimpleGraph V}
    {H : SimpleGraph W} (hr : ∀ x y, G.Adj x y ↔ H.Adj (f x) (f y))
    {S : Finset V} {Q : Finset (Finset W)} (hQ : StableOn H (S.image f) Q) :
    StableOn G S (pullParts f S Q) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B hb
    obtain ⟨C, hc, rfl⟩ := mem_image.mp hb
    obtain ⟨w, hw⟩ := (hQ.1 C hc).1
    obtain ⟨x, hx, hfx⟩ := mem_image.mp (stable_subset hQ hc hw)
    refine ⟨⟨x, mem_filter.mpr ⟨hx, hfx.symm ▸ hw⟩⟩, ?_⟩
    intro x hx y hy hxy hAdj
    exact (hQ.1 C hc).2 (mem_filter.mp hx).2 (mem_filter.mp hy).2
      (fun he => hxy (hf he)) ((hr x y).mp hAdj)
  · intro B hb C hc hBC
    obtain ⟨D, hd, rfl⟩ := mem_image.mp hb
    obtain ⟨E, he, rfl⟩ := mem_image.mp hc
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (hQ.2.1 D hd E he (fun h => hBC (congrArg
      (fun C => S.filter (fun x => f x ∈ C)) h))) (mem_filter.mp hx).2 (mem_filter.mp hy).2
  · ext x
    simp only [pullParts, mem_biUnion, mem_image, id_eq]
    constructor
    · rintro ⟨B, ⟨C, hc, rfl⟩, hx⟩
      exact (mem_filter.mp hx).1
    · intro hx
      have hfS : f x ∈ S.image f := mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨C, hc, hfx⟩ := mem_biUnion.mp (show f x ∈ Q.biUnion id by rwa [hQ.2.2])
      exact ⟨S.filter (fun x => f x ∈ C), ⟨C, hc, rfl⟩, mem_filter.mpr ⟨hx, hfx⟩⟩

lemma pull_map {f : V → W} (hf : Function.Injective f) {G : SimpleGraph V}
    {S : Finset V} {P : Finset (Finset V)} (hP : StableOn G S P) :
    pullParts f S (mapParts f P) = P := by
  classical
  have h : ∀ B ∈ P, S.filter (fun x => f x ∈ B.image f) = B := by
    intro B hb
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, he⟩ := mem_image.mp (mem_filter.mp hx).2
      exact hf he ▸ hy
    · intro hx
      exact mem_filter.mpr ⟨stable_subset hP hb hx, mem_image.mpr ⟨x, hx, rfl⟩⟩
  unfold pullParts mapParts
  rw [image_image]
  have : P.image (fun B => S.filter (fun x => f x ∈ B.image f)) = P.image id :=
    image_congr (fun B hb => h B hb)
  change P.image (fun B => S.filter (fun x => f x ∈ B.image f)) = P
  simpa only [Finset.image_id] using this

lemma map_pull {f : V → W} {H : SimpleGraph W}
    {S : Finset V} {Q : Finset (Finset W)} (hQ : StableOn H (S.image f) Q) :
    mapParts f (pullParts f S Q) = Q := by
  classical
  have h : ∀ C ∈ Q, (S.filter (fun x => f x ∈ C)).image f = C := by
    intro C hc
    ext w
    constructor
    · rintro hw
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hw
      exact (mem_filter.mp hx).2
    · intro hw
      obtain ⟨x, hx, he⟩ := mem_image.mp (stable_subset hQ hc hw)
      exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, he.symm ▸ hw⟩, he⟩
  unfold mapParts pullParts
  rw [image_image]
  have : Q.image (fun C => (S.filter (fun x => f x ∈ C)).image f) = Q.image id :=
    image_congr (fun C hc => h C hc)
  change Q.image (fun C => (S.filter (fun x => f x ∈ C)).image f) = Q
  simpa only [Finset.image_id] using this

lemma count_transport {f : V → W} (hf : Function.Injective f) {G : SimpleGraph V}
    {H : SimpleGraph W} (hr : ∀ x y, G.Adj x y ↔ H.Adj (f x) (f y))
    (S : Finset V) (k : ℕ) : count G S k = count H (S.image f) k := by
  classical
  apply Nat.card_congr
  exact
    { toFun := fun P => ⟨⟨mapParts f P.val.val, map_stable hf hr P.val.property⟩,
        (mapParts_card hf _).trans P.property⟩
      invFun := fun Q => ⟨⟨pullParts f S Q.val.val, pull_stable hf hr Q.val.property⟩, by
        have h := congrArg Finset.card (map_pull Q.val.property)
        rwa [mapParts_card hf, Q.property] at h⟩
      left_inv := fun P => Subtype.ext (Subtype.ext (pull_map hf P.val.property))
      right_inv := fun Q => Subtype.ext (Subtype.ext (map_pull Q.val.property)) }

end GraphicalBellProof
