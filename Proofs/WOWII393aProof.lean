import FormalConjectures.WrittenOnTheWallII.GraphConjecture393
import Proofs.FiniteMatchingCover
import Proofs.PendantSupport

/-!
# The remaining WOWII 393a matching bound

The construction is the one in Gebendorfer's source manuscript. The underlying
domination/matching bound is credited there to DeLaVina--Larson--Pepper--Waller.
Only a lower bound on the combined matching is needed; no equality of matching
parameters is assumed.
-/
namespace WOWII393aProof
open SimpleGraph Finset FiniteMatchingCover
open WrittenOnTheWallII.GraphConjecture393
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem conjecture393a (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (horder : 2 < Fintype.card V) :
    (twoDominationNumber G : ℝ) ≤ (remainder G).card +
      matchingNumberOn G (neighbors G (supports G)) + (pendants G).card := by
  classical
  let P := pendants G
  let S := supports G
  let R := neighbors G S
  let U := univ \ R
  let W := S ∩ R
  let A := R \ (S ∪ P)
  have hP : ∀ p, p ∈ P ↔ G.degree p = 1 := by intro p; simp [P,pendants]
  have hS : ∀ s, s ∈ S ↔ ∃ p ∈ P, G.Adj p s := by
    intro s; simp [S,supports,neighbors,P]
  have hR : ∀ v, v ∈ R ↔ ∃ s ∈ S, G.Adj s v := by intro v; simp [R,neighbors]
  have hPS : Disjoint P S := by
    apply Finset.disjoint_left.mpr
    intro p hp hs
    obtain ⟨q,hq,hqp⟩ := (hS p).mp hs
    exact PendantSupport.leaf_neighbor_not_leaf G hG horder ((hP q).mp hq) hqp ((hP p).mp hp)
  have hPR : P ⊆ R := by
    intro p hp
    obtain ⟨s,hps,_⟩ := degree_eq_one_iff_existsUnique_adj.mp ((hP p).mp hp)
    exact (hR p).mpr ⟨s,(hS s).mpr ⟨p,hp,hps⟩,hps.symm⟩
  have hchoose : ∀ s : (W : Set V), ∃ p ∈ P, G.Adj s.val p := by
    intro s
    obtain ⟨p,hp,hps⟩ := (hS s.val).mp (mem_inter.mp s.property).1
    exact ⟨p,hp,hps.symm⟩
  choose leaf hleafP hleafAdj using hchoose
  have hleafInj : Function.Injective leaf := by
    intro s t he
    obtain ⟨q,_,hq⟩ := degree_eq_one_iff_existsUnique_adj.mp ((hP (leaf s)).mp (hleafP s))
    apply Subtype.ext
    exact (hq s.val (hleafAdj s).symm).trans
      (hq t.val (he ▸ (hleafAdj t).symm)).symm
  let E := (univ : Finset (W : Set V)).image fun s => s(s.val,leaf s)
  have hEvalid : Valid G E := by
    constructor
    · intro e he
      obtain ⟨s,_,rfl⟩ := mem_image.mp he
      exact hleafAdj s
    · intro e he f hf v hve hvf
      obtain ⟨s,_,rfl⟩ := mem_image.mp he
      obtain ⟨t,_,rfl⟩ := mem_image.mp hf
      have hst : s = t := by
        rcases Sym2.mem_iff.mp hve with hs | hs <;>
          rcases Sym2.mem_iff.mp hvf with ht | ht
        · exact Subtype.ext (hs.symm.trans ht)
        · exact (Finset.disjoint_left.mp hPS (hleafP t)
            ((hs.symm.trans ht) ▸ (mem_inter.mp s.property).1)).elim
        · exact (Finset.disjoint_left.mp hPS (hleafP s)
            ((ht.symm.trans hs) ▸ (mem_inter.mp t.property).1)).elim
        · exact hleafInj (hs.symm.trans ht)
      subst t; rfl
  have hEverts : vertices E ⊆ W ∪ P := by
    intro v hv
    obtain ⟨e,he,hve⟩ := mem_vertices.mp hv
    obtain ⟨s,_,rfl⟩ := mem_image.mp he
    rcases Sym2.mem_iff.mp hve with rfl | rfl
    · exact mem_union_left _ s.property
    · exact mem_union_right _ (hleafP s)
  have hEcard : E.card = W.card := by
    rw [card_image_of_injective, card_univ]
    · rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    ·
      intro s t he
      rcases Sym2.eq_iff.mp he with he | he
      · exact Subtype.ext he.1
      · exact (Finset.disjoint_left.mp hPS (hleafP t)
          (he.1 ▸ (mem_inter.mp s.property).1)).elim
  let H := G.induce (A : Set V)
  obtain ⟨M,hM,Q,hQcard,_hQverts,hQdom⟩ := dominating_selection H
  let M' := M.image (Sym2.map Subtype.val)
  let Q' := Q.image Subtype.val
  have hM' : Valid G M' := map_valid Subtype.val Subtype.val_injective (fun h => h) hM
  have hM'A : vertices M' ⊆ A := by
    rw [vertices_map]
    intro v hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hv
    exact w.property
  have hQ'A : Q' ⊆ A := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hv
    exact w.property
  have hdis : Disjoint (vertices E) (vertices M') := by
    apply Finset.disjoint_left.mpr
    intro v hvE hvM
    have hvA := mem_sdiff.mp (hM'A hvM)
    rcases mem_union.mp (hEverts hvE) with hvW | hvP
    · exact hvA.2 (mem_union_left _ (mem_inter.mp hvW).1)
    · exact hvA.2 (mem_union_right _ hvP)
  have hEm : Disjoint E M' := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Finset.disjoint_left.mp hdis
      (mem_vertices.mpr ⟨e,he,Sym2.out_fst_mem e⟩)
      (mem_vertices.mpr ⟨e,hf,Sym2.out_fst_mem e⟩)
  have htotal : Valid G (E ∪ M') := union_valid hEvalid hM' hdis
  have htotalR : vertices (E ∪ M') ⊆ R := by
    intro v hv
    obtain ⟨e,he,hve⟩ := mem_vertices.mp hv
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp (hEverts (mem_vertices.mpr ⟨_,he,hve⟩)) with hw | hp
      · exact (mem_inter.mp hw).2
      · exact hPR hp
    · exact (mem_sdiff.mp (hM'A (mem_vertices.mpr ⟨_,he,hve⟩))).1
  have hmu := card_le_matchingNumber_on G R (E ∪ M') htotal htotalR
  have hMcard : M'.card = M.card := card_image_of_injective _
    (Sym2.map.injective Subtype.val_injective)
  rw [card_union_of_disjoint hEm,hEcard,hMcard] at hmu
  let D := ((U ∪ P) ∪ W) ∪ Q'
  have hSD : S ⊆ D := by
    intro s hs
    by_cases hsR : s ∈ R
    · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hs,hsR⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (by simp [U,hsR])))
  have hPD : P ⊆ D := by
    intro p hp; exact mem_union_left _ (mem_union_left _ (mem_union_right _ hp))
  have hout : ∀ v, v ∉ D → v ∈ A := by
    intro v hv
    have hvR : v ∈ R := by
      by_contra hn
      exact hv (mem_union_left _ (mem_union_left _ (mem_union_left _ (by simp [U,hn]))))
    refine mem_sdiff.mpr ⟨hvR,?_⟩
    intro hsp
    rcases mem_union.mp hsp with hs | hp
    · exact hv (hSD hs)
    · exact hv (hPD hp)
  have hD : IsTwoDominating G D := by
    intro v hvD
    have hvA := hout v hvD
    let vA : (A : Set V) := ⟨v,hvA⟩
    by_cases hh : ∃ w : (A : Set V), H.Adj vA w
    · have hvQ : vA ∉ Q := by
        intro hvQ
        exact hvD (mem_union_right _ (mem_image_of_mem Subtype.val hvQ))
      obtain ⟨q,hq,hvq⟩ := hQdom vA hh hvQ
      obtain ⟨s,hs,hsv⟩ := (hR v).mp (mem_sdiff.mp hvA).1
      have hqs : q.val ≠ s := by
        intro he
        exact (mem_sdiff.mp q.property).2 (mem_union_left _ (he ▸ hs))
      have hsub : {q.val,s} ⊆ G.neighborFinset v ∩ D := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact mem_inter.mpr ⟨by simpa [H,vA] using hvq,
            mem_union_right _ (mem_image_of_mem Subtype.val hq)⟩
        · have : w = s := mem_singleton.mp hw
          subst w
          exact mem_inter.mpr ⟨by simpa using hsv.symm,hSD hs⟩
      have hc := card_le_card hsub
      simpa [hqs] using hc
    · have hsub : G.neighborFinset v ⊆ D := by
        intro w hw
        by_contra hwD
        exact hh ⟨⟨w,hout w hwD⟩,by simpa [H,vA] using hw⟩
      have heq : G.neighborFinset v ∩ D = G.neighborFinset v := inter_eq_left.mpr hsub
      rw [heq, card_neighborFinset_eq_degree]
      have hn1 : G.degree v ≠ 1 := by
        intro he
        exact hvD (hPD ((hP v).mpr he))
      let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hp := hG.preconnected.degree_pos_of_nontrivial v
      omega
  have hnum : twoDominationNumber G ≤ D.card := Nat.sInf_le ⟨D,hD,rfl⟩
  have hcard : D.card ≤ U.card + P.card + W.card + M.card := by
    have h1 := card_union_le ((U ∪ P) ∪ W) Q'
    have h2 := card_union_le (U ∪ P) W
    have h3 := card_union_le U P
    have h4 : Q'.card ≤ Q.card := card_image_le
    dsimp [D]
    omega
  have hnat := hnum.trans hcard
  have hreal : (twoDominationNumber G : ℝ) ≤ U.card + P.card + W.card + M.card := by
    exact_mod_cast hnat
  change (twoDominationNumber G : ℝ) ≤ U.card +
    matchingNumberOn G R + P.card
  change ((W.card + M.card : ℕ) : ℝ) ≤ matchingNumberOn G R at hmu
  push_cast at hmu
  linarith

end WOWII393aProof
