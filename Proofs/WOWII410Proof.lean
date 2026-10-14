/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.CriticalIndependentProof

/-! Complete universal proofs of WOWII410a and410b. Written source: Jonas J.
Gebendorfer, A Regular-Graph Dichotomy for Maximum Critical Independent Sets,
31 August2026 R1. The source already notes the immediate nonregular case. -/
namespace WOWII410Proof
open SimpleGraph Finset CriticalIndependentProof
variable {V : Type*} [Fintype V] [DecidableEq V]

def minimumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V := univ.filter fun v => ∀ w, G.degree v ≤ G.degree w
def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V := univ.filter fun v => ∀ w, G.degree w ≤ G.degree v
noncomputable def evenCount (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (univ.filter fun w => Even (G.dist v w)).card
noncomputable def evenMax (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, evenCount G w ≤ evenCount G v
noncomputable def evenMin (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, evenCount G v ≤ evenCount G w
def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V) : ℕ := (G.edgeFinset.filter fun e => e.toFinset ⊆ Q).card
def baseBound (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ \ minimumVertices G).card + (univ \ maximumVertices G).card

omit [DecidableEq V] in
lemma closed_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) {R : Finset V}
    (hn : R.Nonempty) (hclose : ∀ u ∈ R, ∀ v, G.Adj u v → v ∈ R) : R = univ := by
  classical
  obtain ⟨r, hr⟩ := hn
  have step : ∀ {u v}, G.Walk u v → u ∈ R → v ∈ R := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons u a v hua tail ih => exact fun hu => ih (hclose u hu a hua)
  apply eq_univ_of_forall
  intro v
  obtain ⟨w⟩ := hc r v
  exact step w hr

lemma regular_positive (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 2 < Fintype.card V) {k : ℕ} (hk : ∀ v, G.degree v = k) : 2 ≤ k := by
  classical
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x⟩ := hc.nonempty
  have hp : 0 < k := (hk x) ▸ hc.preconnected.degree_pos_of_nontrivial x
  by_contra h
  have hk1 : k = 1 := by omega
  have deg1 : ∀ v, G.degree v = 1 := fun v => (hk v).trans hk1
  obtain ⟨y, hxy, hxu⟩ := G.degree_eq_one_iff_existsUnique_adj.mp (deg1 x)
  obtain ⟨z, hyz, hyu⟩ := G.degree_eq_one_iff_existsUnique_adj.mp (deg1 y)
  have hzy : z = x := (hyu _ hxy.symm).symm
  subst z
  have hcover : ({x, y} : Finset V) = univ := closed_cover G hc (by simp) (by
    intro u hu v huv
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · simp [hxu _ huv]
    · simp [hyu _ huv])
  have hh := congrArg card hcover
  have hb : ({x, y} : Finset V).card ≤ 2 := by simpa using (card_insert_le x ({y} : Finset V))
  rw [card_univ] at hh
  omega

omit [DecidableEq V] in
lemma cross_sum (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) :
    (∑ u ∈ I, G.degree u) =
      ∑ v ∈ neighborhood G I, (I.filter fun u => G.Adj u v).card := by
  classical
  have he (u : V) (hu : u ∈ I) :
      (neighborhood G I).bipartiteAbove G.Adj u = G.neighborFinset u := by
    ext v
    simp only [mem_bipartiteAbove, mem_neighborFinset, mem_neighborhood]
    exact ⟨And.right, fun h => ⟨⟨u, hu, h⟩, h⟩⟩
  calc
    _ = ∑ u ∈ I, ((neighborhood G I).bipartiteAbove G.Adj u).card := by
      apply sum_congr rfl; intro u hu; rw [he u hu]; rfl
    _ = _ := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

omit [DecidableEq V] in
lemma regular_critical_saturated (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : ∀ v, G.degree v = k) (hkp : 0 < k)
    {I : Finset V} (hI : IsCritical G I) :
    I.card = (neighborhood G I).card ∧
      ∀ v ∈ neighborhood G I, G.neighborFinset v ⊆ I := by
  classical
  have hle (v : V) : (I.filter fun u => G.Adj u v).card ≤ k := by
    rw [← hk v, ← G.card_neighborFinset_eq_degree]
    apply card_le_card
    intro u hu
    exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hu).2.symm
  have hs := cross_sum G I
  simp only [hk, sum_const, smul_eq_mul] at hs
  have hbound : I.card * k ≤ (neighborhood G I).card * k := by
    rw [hs]
    simpa only [sum_const, smul_eq_mul] using
      (sum_le_sum (s := neighborhood G I) (fun v _ => hle v))
  have hic : I.card ≤ (neighborhood G I).card := Nat.le_of_mul_le_mul_right hbound hkp
  have hrev : (neighborhood G I).card ≤ I.card := by
    have := critical_nonnegative G hI
    unfold difference at this
    omega
  have heq : I.card = (neighborhood G I).card := Nat.le_antisymm hic hrev
  refine ⟨heq, ?_⟩
  intro v hv
  have hvc : (I.filter fun u => G.Adj u v).card = k := by
    by_contra hne
    have hstrict : (∑ w ∈ neighborhood G I, (I.filter fun u => G.Adj u w).card) <
        ∑ _w ∈ neighborhood G I, k :=
      sum_lt_sum (fun w _ => hle w) ⟨v, hv, lt_of_le_of_ne (hle v) hne⟩
    simp only [sum_const, smul_eq_mul] at hstrict
    rw [heq] at hs
    omega
  have hs' : I.filter (fun u => G.Adj u v) ⊆ G.neighborFinset v := by
    intro u hu; exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hu).2.symm
  have he : I.filter (fun u => G.Adj u v) = G.neighborFinset v :=
    eq_of_subset_of_card_le hs' (by rw [hvc, G.card_neighborFinset_eq_degree, hk])
  rw [← he]
  exact filter_subset _ _

lemma critical_partition (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) {k : ℕ}
    (hk : ∀ v, G.degree v = k) (hkp : 0 < k)
    {I : Finset V} (hI : IsCritical G I) (hn : I.Nonempty) :
    I ∪ neighborhood G I = univ ∧ Disjoint I (neighborhood G I) ∧
      I.card = (neighborhood G I).card ∧
      ∀ u v, G.Adj u v → (u ∈ I ↔ v ∉ I) := by
  classical
  obtain ⟨heq, hs⟩ := regular_critical_saturated G hk hkp hI
  have hd : Disjoint I (neighborhood G I) := by
    apply Finset.disjoint_left.mpr
    intro u hu hnu
    obtain ⟨v, hv, he⟩ := (mem_neighborhood G I u).mp hnu
    exact independent_no_edge G hI.1 hv hu he
  have hcover : I ∪ neighborhood G I = univ := closed_cover G hc
    (hn.mono subset_union_left) (by
      intro u hu v huv
      rcases mem_union.mp hu with hu | hu
      · exact mem_union_right _ ((mem_neighborhood G I v).mpr ⟨u, hu, huv⟩)
      · exact mem_union_left _ (hs u hu ((G.mem_neighborFinset _ _).mpr huv)))
  refine ⟨hcover, hd, heq, ?_⟩
  intro u v huv
  constructor
  · intro hu hv; exact independent_no_edge G hI.1 hu hv huv
  · intro hv
    have hvm : v ∈ I ∪ neighborhood G I := by rw [hcover]; exact mem_univ _
    exact hs v ((mem_union.mp hvm).resolve_left hv) ((G.mem_neighborFinset _ _).mpr huv.symm)

omit [Fintype V] in
lemma walk_parity (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V)
    (hflip : ∀ u v, G.Adj u v → (u ∈ I ↔ v ∉ I))
    {u v : V} (w : G.Walk u v) : Even w.length ↔ (u ∈ I ↔ v ∈ I) := by
  classical
  induction w with
  | nil => simp
  | @cons u a v hua tail ih =>
    have hf := hflip u a hua
    rw [Walk.length_cons, Nat.even_add_one, ih]
    tauto

lemma even_constant_of_partition (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) (I : Finset V)
    (hcover : I ∪ neighborhood G I = univ) (hd : Disjoint I (neighborhood G I))
    (heq : I.card = (neighborhood G I).card)
    (hflip : ∀ u v, G.Adj u v → (u ∈ I ↔ v ∉ I)) :
    ∀ v, evenCount G v = I.card := by
  classical
  intro v
  have hp (w : V) : Even (G.dist v w) ↔ (v ∈ I ↔ w ∈ I) := by
    obtain ⟨p, hlen⟩ := hc.exists_walk_length_eq_dist v w
    rw [← hlen]
    exact walk_parity G I hflip p
  by_cases hv : v ∈ I
  · have hh : (univ.filter fun w => Even (G.dist v w)) = I := by
      ext w; simp [hp, hv]
    exact congrArg card hh
  · have hcI : univ \ I = neighborhood G I := by
      ext w
      have hall : w ∈ I ∨ w ∈ neighborhood G I := by
        rw [← mem_union, hcover]; exact mem_univ _
      have hn := Finset.disjoint_left.mp hd
      simp only [mem_sdiff, mem_univ, true_and]
      tauto
    have hh : (univ.filter fun w => Even (G.dist v w)) = univ \ I := by
      ext w; simp [hp, hv]
    change (univ.filter fun w => Even (G.dist v w)).card = _
    rw [hh, hcI, heq]

/-- If H is nonempty in a connected positive-regular graph, all even counts agree. -/
lemma even_constant_of_union (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    {k : ℕ} (hk : ∀ v, G.degree v = k) (hkp : 0 < k)
    (hH : (criticalUnion G).Nonempty) : ∃ c, ∀ v, evenCount G v = c := by
  obtain ⟨v, hv⟩ := hH
  obtain ⟨I, hI, hvI⟩ := (mem_criticalUnion G v).mp hv
  obtain ⟨hcover, hd, heq, hf⟩ := critical_partition G hc hk hkp hI.1 ⟨v, hvI⟩
  exact ⟨I.card, even_constant_of_partition G hc I hcover hd heq hf⟩

lemma bound_for_extremum (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 2 < Fintype.card V) (D : Finset V)
    (hD : (∃ c, ∀ v, evenCount G v = c) → D = univ) :
    (criticalUnion G).card ≤ baseBound G + edgesOn G D := by
  classical
  by_cases hreg : ∃ k, ∀ v, G.degree v = k
  · obtain ⟨k, hk⟩ := hreg
    have hkp := regular_positive G hc hn hk
    by_cases hH : (criticalUnion G).Nonempty
    · have hDu := hD (even_constant_of_union G hc hk (by omega) hH)
      have hedge : edgesOn G D = G.edgeFinset.card := by
        simp [edgesOn, hDu]
      have hsum := G.sum_degrees_eq_twice_card_edges
      simp only [hk, sum_const, card_univ, smul_eq_mul] at hsum
      have hm : Fintype.card V ≤ G.edgeFinset.card := by nlinarith
      exact (card_le_univ _).trans (by rw [hedge]; omega)
    · have hz : criticalUnion G = ∅ := not_nonempty_iff_eq_empty.mp hH
      simp [hz]
  · have hdis : Disjoint (minimumVertices G) (maximumVertices G) := by
      apply Finset.disjoint_left.mpr
      intro v hv hm
      have hmin := (mem_filter.mp hv).2
      have hmax := (mem_filter.mp hm).2
      exact hreg ⟨G.degree v, fun w => Nat.le_antisymm (hmax w) (hmin w)⟩
    have hcard := card_union_of_disjoint hdis
    have hle := card_le_univ (minimumVertices G ∪ maximumVertices G)
    have ha := card_le_univ (minimumVertices G)
    have hm := card_le_univ (maximumVertices G)
    have hb : Fintype.card V ≤ baseBound G := by
      simp only [baseBound, card_sdiff_of_subset (subset_univ _), card_univ]
      omega
    exact (card_le_univ _).trans (by omega)

theorem conjecture410a (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 2 < Fintype.card V) :
    (criticalUnion G).card ≤ baseBound G + edgesOn G (evenMax G) := by
  apply bound_for_extremum G hc hn
  rintro ⟨c, he⟩
  simp [evenMax, he]

theorem conjecture410b (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 2 < Fintype.card V) :
    (criticalUnion G).card ≤ baseBound G + edgesOn G (evenMin G) := by
  apply bound_for_extremum G hc hn
  rintro ⟨c, he⟩
  simp [evenMin, he]

noncomputable def positiveEvenCount (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (univ.filter fun w => 0 < G.dist v w ∧ Even (G.dist v w)).card

lemma distance_zero_convention (G : SimpleGraph V) (hc : G.Connected) (v : V) :
    evenCount G v = positiveEvenCount G v + 1 := by
  classical
  let E := univ.filter fun w => Even (G.dist v w)
  have hv : v ∈ E := by simp [E]
  have he : (univ.filter fun w => 0 < G.dist v w ∧ Even (G.dist v w)) = E.erase v := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_erase, E]
    have hz := hc.dist_eq_zero_iff (u := v) (v := w)
    constructor
    · rintro ⟨hp, he⟩; exact ⟨by intro h; subst w; simp at hp, he⟩
    · rintro ⟨hne, he⟩
      exact ⟨Nat.pos_of_ne_zero (fun hh => hne (hz.mp hh).symm), he⟩
  have hcE := card_erase_of_mem hv
  have hp := card_pos.mpr ⟨v, hv⟩
  change E.card = (univ.filter fun w => 0 < G.dist v w ∧ Even (G.dist v w)).card + 1
  rw [he, hcE]
  omega

lemma positive_extrema_unchanged (G : SimpleGraph V) (hc : G.Connected) :
    evenMax G = (univ.filter fun v => ∀ w, positiveEvenCount G w ≤ positiveEvenCount G v) ∧
    evenMin G = (univ.filter fun v => ∀ w, positiveEvenCount G v ≤ positiveEvenCount G w) := by
  classical
  have hle (u v : V) : evenCount G u ≤ evenCount G v ↔
      positiveEvenCount G u ≤ positiveEvenCount G v := by
    rw [distance_zero_convention G hc u, distance_zero_convention G hc v]
    omega
  constructor <;> ext v <;> simp [evenMax, evenMin, hle]
end WOWII410Proof
