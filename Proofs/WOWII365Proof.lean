import FormalConjectures.WrittenOnTheWallII.GraphConjecture365

/-! Kernel proof of WOWII 365 and its integer strengthening.
The counting argument follows Gebendorfer's manuscript linked in PR 7370.
OpenAI Codex assisted with formalization. -/

namespace WOWII365Proof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture365

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : SimpleGraph V) [DecidableRel T.Adj]

def innerEdges (S : Finset V) : Finset (Sym2 V) :=
  T.edgeFinset.filter fun e => e.toFinset ⊆ S

@[simp] lemma mem_innerEdges (S : Finset V) (u v : V) :
    s(u,v) ∈ innerEdges T S ↔ T.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp [innerEdges, Sym2.toFinset_mk_eq, insert_subset_iff]

lemma forest_budget (hT : T.IsTree) (D I : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) (hID : I ⊆ D)
    (hI : T.IsIndepSet (I : Set V)) :
    I.card + (innerEdges T (univ \ D)).card + 1 ≤ D.card := by
  classical
  choose f hfD hf using hD
  let X := univ \ D
  let H := X ∪ I
  let E := H.image fun v => s(v, f v)
  have hX : ∀ v ∈ X, v ∉ D := by simp [X]
  have hInj : Set.InjOn (fun v => s(v, f v)) (H : Set V) := by
    intro u hu v hv he
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.1
    · have huD : u ∈ D := by rw [h.1]; exact hfD v
      have hvD : v ∈ D := by rw [← h.2]; exact hfD u
      have huI : u ∈ I := (mem_union.mp hu).resolve_left (fun hx => hX u hx huD)
      have hvI : v ∈ I := (mem_union.mp hv).resolve_left (fun hx => hX v hx hvD)
      exact False.elim (hI huI hvI (by simpa [h.2] using (hf u).ne)
        (by simpa [h.2] using hf u))
  have hEcard : E.card = H.card := card_image_of_injOn hInj
  have hEH : E ⊆ T.edgeFinset := by
    intro e he
    obtain ⟨v, _, rfl⟩ := mem_image.mp he
    simpa using hf v
  have hdis : Disjoint E (innerEdges T X) := by
    apply Finset.disjoint_left.mpr
    intro e he heX
    obtain ⟨v, _, rfl⟩ := mem_image.mp he
    have hfv := (mem_innerEdges T X v (f v)).mp heX
    exact hX (f v) hfv.2.2 (hfD v)
  have hsub : E ∪ innerEdges T X ⊆ T.edgeFinset := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hEH he
    · exact (mem_filter.mp he).1
  have hbound := card_le_card hsub
  rw [card_union_of_disjoint hdis, hEcard] at hbound
  have hXI : Disjoint X I := Finset.disjoint_left.mpr fun v hx hi => hX v hx (hID hi)
  have hHcard : H.card = X.card + I.card := card_union_of_disjoint hXI
  have htotal : X.card + D.card = Fintype.card V := by
    dsimp [X]
    rw [card_sdiff_of_subset (subset_univ D), card_univ]
    exact Nat.sub_add_cancel (card_le_univ D)
  have htree := hT.card_edgeFinset
  dsimp [X] at hbound hHcard htotal
  omega

omit [DecidableEq V] in
lemma supports_forced (D : Finset V) (hD : T.IsTotalDominating (D : Set V)) :
    supports T ⊆ D := by
  intro s hs
  obtain ⟨p, hp, hsp⟩ := (mem_filter.mp hs).2
  obtain ⟨w, hwD, hpw⟩ := hD p
  obtain ⟨q, _, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hp
  have hws : w = s := (huniq w hpw).trans (huniq s hsp.symm).symm
  exact hws ▸ hwD

omit [DecidableEq V] in
lemma mem_isolated (v : V) : v ∈ isolatedSupports T ↔
    v ∈ supports T ∧ ∀ w ∈ supports T, ¬ T.Adj v w := by
  simp only [isolatedSupports, mem_filter]

omit [DecidableEq V] in
lemma isolated_subset : isolatedSupports T ⊆ supports T := by
  intro v hv
  exact ((mem_isolated T v).mp hv).1

omit [DecidableEq V] in
lemma isolated_independent : T.IsIndepSet (isolatedSupports T : Set V) := by
  intro u hu v hv _ huv
  exact ((mem_isolated T u).mp hu).2 v ((mem_isolated T v).mp hv).1 huv

omit [DecidableEq V] in
lemma two_neighbors (v p u : V) (hv : T.degree v = 2)
    (hvp : T.Adj v p) (hvu : T.Adj v u) (hpu : p ≠ u) :
    ∀ w, T.Adj v w → w = p ∨ w = u := by
  classical
  have hsub : {p,u} ⊆ T.neighborFinset v := by
    intro w hw
    rcases mem_insert.mp hw with h | h
    · subst w; exact (mem_neighborFinset T v p).mpr hvp
    · have : w = u := mem_singleton.mp h
      subst w; exact (mem_neighborFinset T v u).mpr hvu
  have heq : T.neighborFinset v = {p,u} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le hsub
    simpa [hpu] using hv.le
  intro w hw
  have : w ∈ ({p,u} : Finset V) := heq ▸ (mem_neighborFinset T v w).mpr hw
  simpa using this

omit [DecidableEq V] in
lemma leaf_not_support (v p : V) (hv : T.degree v = 2)
    (hp : T.degree p = 1) (hvp : T.Adj v p) : p ∉ supports T := by
  intro hs
  obtain ⟨q, hq, hpq⟩ := (mem_filter.mp hs).2
  obtain ⟨a, _, ha⟩ := degree_eq_one_iff_existsUnique_adj.mp hp
  have hqv : q = v := (ha q hpq).trans (ha v hvp.symm).symm
  rw [hqv, hv] at hq
  omega

def incidentTwo (v : V) : Finset (Sym2 V) :=
  (innerEdges T (degreeTwo T)).filter fun e => v ∈ e

lemma incidentTwo_le (v : V) : (incidentTwo T v).card ≤ T.degree v := by
  rw [← T.card_incidenceFinset_eq_degree v]
  apply card_le_card
  intro e he
  have he' := mem_filter.mp he
  rw [T.incidenceFinset_eq_filter]
  exact mem_filter.mpr ⟨(mem_filter.mp he'.1).1, he'.2⟩

lemma incidentTwo_support_le (v : V) (hv : T.degree v = 2)
    (hs : v ∈ supports T) : (incidentTwo T v).card ≤ 1 := by
  obtain ⟨p, hp, hvp⟩ := (mem_filter.mp hs).2
  have hedge : s(v,p) ∈ T.incidenceFinset v := by
    rw [T.incidenceFinset_eq_filter]
    simp [hvp]
  have hnot : s(v,p) ∉ incidentTwo T v := by
    intro he
    have hpd := ((mem_innerEdges T (degreeTwo T) v p).mp (mem_filter.mp he).1).2.2
    have : T.degree p = 2 := (mem_filter.mp hpd).2
    omega
  have hsub : incidentTwo T v ⊆ (T.incidenceFinset v).erase s(v,p) := by
    intro e he
    apply mem_erase.mpr
    refine ⟨fun h => hnot (h ▸ he), ?_⟩
    rw [T.incidenceFinset_eq_filter]
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp he).1).1, (mem_filter.mp he).2⟩
  have := card_le_card hsub
  rw [card_erase_of_mem hedge, T.card_incidenceFinset_eq_degree, hv] at this
  exact this

def badSupports (D : Finset V) : Finset V :=
  (isolatedSupports T ∩ degreeTwo T).filter fun v =>
    ∃ u ∈ degreeTwo T, T.Adj v u ∧ u ∉ D

lemma bad_support_selected_leaf (D : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) (v : V) (hv : v ∈ badSupports T D) :
    ∃ p ∈ D \ isolatedSupports T, T.degree p = 1 ∧ T.Adj v p := by
  have hv' := mem_filter.mp hv
  have hvI := (mem_inter.mp hv'.1).1
  have hv2 : T.degree v = 2 := (mem_filter.mp (mem_inter.mp hv'.1).2).2
  obtain ⟨u, hu, hvu, huD⟩ := hv'.2
  have hu2 : T.degree u = 2 := (mem_filter.mp hu).2
  obtain ⟨p, hp, hvp⟩ := (mem_filter.mp ((mem_isolated T v).mp hvI).1).2
  have hpu : p ≠ u := by intro h; rw [h, hu2] at hp; omega
  obtain ⟨w, hwD, hvw⟩ := hD v
  have hwp : w = p := (two_neighbors T v p u hv2 hvp hvu hpu w hvw).resolve_right
    (fun hwu => huD (hwu ▸ hwD))
  subst w
  refine ⟨p, mem_sdiff.mpr ⟨hwD, ?_⟩, hp, hvp⟩
  exact fun hpi => leaf_not_support T v p hv2 hp hvp ((mem_isolated T p).mp hpi).1

lemma bad_support_card (D : Finset V) (hD : T.IsTotalDominating (D : Set V)) :
    (badSupports T D).card ≤ ((D \ isolatedSupports T).filter fun p => T.degree p = 1).card := by
  classical
  have hex := bad_support_selected_leaf T D hD
  choose f hf using fun v : {v // v ∈ badSupports T D} => hex v v.property
  let g : {v // v ∈ badSupports T D} →
      {p // p ∈ ((D \ isolatedSupports T).filter fun p => T.degree p = 1)} :=
    fun v => ⟨f v, mem_filter.mpr ⟨(hf v).1, (hf v).2.1⟩⟩
  apply card_le_card_of_injective (f := g)
  intro v u he
  have he' : f v = f u := congrArg Subtype.val he
  have hp := (hf v).2.1
  obtain ⟨q, _, hq⟩ := degree_eq_one_iff_existsUnique_adj.mp hp
  have hvp := (hf v).2.2.symm
  have hup : T.Adj (f v) u.val := by rw [he']; exact (hf u).2.2.symm
  exact Subtype.ext ((hq v.val hvp).trans (hq u.val hup).symm)

lemma charge_edges (D : Finset V) (hD : T.IsTotalDominating (D : Set V)) :
    (innerEdges T (degreeTwo T)).card ≤
      2 * ((D \ isolatedSupports T) ∩ degreeTwo T).card +
        ((D \ isolatedSupports T).filter fun p => T.degree p = 1).card +
          (innerEdges T (degreeTwo T \ D)).card := by
  classical
  let I := isolatedSupports T
  let A := (D \ I) ∩ degreeTwo T
  let B := badSupports T D
  let M := innerEdges T (degreeTwo T \ D)
  have hID : I ⊆ D := (isolated_subset T).trans (supports_forced T D hD)
  have hind := isolated_independent T
  have hcover : innerEdges T (degreeTwo T) ⊆
      (A.biUnion (incidentTwo T) ∪ B.biUnion (incidentTwo T)) ∪ M := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      obtain ⟨huv, hu2, hv2⟩ := (mem_innerEdges T (degreeTwo T) u v).mp he
      have hincu : s(u,v) ∈ incidentTwo T u := by simp [incidentTwo, he]
      have hincv : s(u,v) ∈ incidentTwo T v := by simp [incidentTwo, he]
      by_cases huA : u ∈ A
      · exact mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨u, huA, hincu⟩))
      by_cases hvA : v ∈ A
      · exact mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨v, hvA, hincv⟩))
      by_cases huD : u ∈ D
      · have huI : u ∈ I := by
          by_contra hn
          exact huA (mem_inter.mpr ⟨mem_sdiff.mpr ⟨huD, hn⟩, hu2⟩)
        have hvD : v ∉ D := by
          intro hvD
          have hvI : v ∈ I := by
            by_contra hn
            exact hvA (mem_inter.mpr ⟨mem_sdiff.mpr ⟨hvD, hn⟩, hv2⟩)
          exact hind huI hvI huv.ne huv
        have huB : u ∈ B := mem_filter.mpr ⟨mem_inter.mpr ⟨huI, hu2⟩,
          ⟨v, hv2, huv, hvD⟩⟩
        exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨u, huB, hincu⟩))
      by_cases hvD : v ∈ D
      · have hvI : v ∈ I := by
          by_contra hn
          exact hvA (mem_inter.mpr ⟨mem_sdiff.mpr ⟨hvD, hn⟩, hv2⟩)
        have hvB : v ∈ B := mem_filter.mpr ⟨mem_inter.mpr ⟨hvI, hv2⟩,
          ⟨u, hu2, huv.symm, huD⟩⟩
        exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨v, hvB, hincv⟩))
      · exact mem_union_right _ ((mem_innerEdges T (degreeTwo T \ D) u v).mpr
          ⟨huv, mem_sdiff.mpr ⟨hu2,huD⟩, mem_sdiff.mpr ⟨hv2,hvD⟩⟩)
  have hA : (A.biUnion (incidentTwo T)).card ≤ 2 * A.card := by
    calc
      _ ≤ ∑ v ∈ A, (incidentTwo T v).card := card_biUnion_le
      _ ≤ ∑ v ∈ A, 2 := sum_le_sum fun v hv =>
        (incidentTwo_le T v).trans (le_of_eq (mem_filter.mp (mem_inter.mp hv).2).2)
      _ = _ := by simp [mul_comm]
  have hB : (B.biUnion (incidentTwo T)).card ≤ B.card := by
    calc
      _ ≤ ∑ v ∈ B, (incidentTwo T v).card := card_biUnion_le
      _ ≤ ∑ v ∈ B, 1 := by
        apply sum_le_sum
        intro v hv
        have hvI := (mem_inter.mp (mem_filter.mp hv).1).1
        have hv2 := (mem_filter.mp (mem_inter.mp (mem_filter.mp hv).1).2).2
        exact incidentTwo_support_le T v hv2 ((mem_isolated T v).mp hvI).1
      _ = _ := by simp
  have hc := (card_le_card hcover).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have hb := bad_support_card T D hD
  change B.card ≤ _ at hb
  change (innerEdges T (degreeTwo T)).card ≤ 2 * A.card + _ + M.card
  omega

lemma degree_two_budget (hT : T.IsTree) (D : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) :
    edgesOn T (degreeTwo T) + 1 ≤ 3 * (D.card - (isolatedSupports T).card) := by
  classical
  let I := isolatedSupports T
  let R := D \ I
  let A := R ∩ degreeTwo T
  let L := R.filter fun p => T.degree p = 1
  have hID : I ⊆ D := (isolated_subset T).trans (supports_forced T D hD)
  have hR : R.card + I.card = D.card := by
    dsimp [R]
    rw [card_sdiff_of_subset hID]
    exact Nat.sub_add_cancel (card_le_card hID)
  have hdis : Disjoint A L := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvL
    have h2 := (mem_filter.mp (mem_inter.mp hvA).2).2
    have h1 := (mem_filter.mp hvL).2
    omega
  have hsub : A ∪ L ⊆ R := union_subset (inter_subset_left) (filter_subset _ _)
  have hsum := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hsum
  have hmono : innerEdges T (degreeTwo T \ D) ⊆ innerEdges T (univ \ D) := by
    intro e he
    obtain ⟨heT, heS⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨heT, heS.trans (sdiff_subset_sdiff (subset_univ _) Subset.rfl)⟩
  have hb := forest_budget T hT D I hD hID (isolated_independent T)
  have hm := card_le_card hmono
  have hc := charge_edges T D hD
  change (innerEdges T (degreeTwo T)).card ≤ 2 * A.card + L.card + _ at hc
  change (innerEdges T (degreeTwo T)).card + 1 ≤ 3 * (D.card - I.card)
  omega

omit [DecidableEq V] [DecidableRel T.Adj] in
lemma minimum_total_set (hT : T.IsTree) (horder : 2 < Fintype.card V) :
    ∃ D : Finset V, T.IsTotalDominating (D : Set V) ∧ D.card = T.totalDominationNumber := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have huniv : T.IsTotalDominating (Set.univ : Set V) := by
    intro v
    obtain ⟨w, hvw⟩ := hT.preconnected.exists_adj_of_nontrivial v
    exact ⟨w, Set.mem_univ w, hvw⟩
  have hn : {n | ∃ D : Finset V, T.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨Fintype.card V, univ, ⟨by simpa using huniv, card_univ⟩⟩
  obtain ⟨D, hD⟩ := csInf_mem hn
  exact ⟨D, hD.isTotalDominating, hD.card_eq⟩

theorem conjecture365_strengthened (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2 < Fintype.card V) :
    (isolatedSupports T).card + edgesOn T (degreeTwo T) / 3 + 1 ≤
      T.totalDominationNumber := by
  obtain ⟨D,hD,hcard⟩ := minimum_total_set T hT horder
  have hb := degree_two_budget T hT D hD
  have hi : (isolatedSupports T).card ≤ D.card :=
    card_le_card ((isolated_subset T).trans (supports_forced T D hD))
  rw [hcard] at hb hi
  omega

theorem conjecture365 (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2 < Fintype.card V) :
    ((isolatedSupports T).card : ℚ) + (edgesOn T (degreeTwo T) : ℚ) / 3 ≤
      T.totalDominationNumber := by
  obtain ⟨D,hD,hcard⟩ := minimum_total_set T hT horder
  have hb := degree_two_budget T hT D hD
  have hi : (isolatedSupports T).card ≤ D.card :=
    card_le_card ((isolated_subset T).trans (supports_forced T D hD))
  have hn : edgesOn T (degreeTwo T) + 1 + 3 * (isolatedSupports T).card ≤ 3 * D.card := by
    omega
  have hq : (edgesOn T (degreeTwo T) : ℚ) + 1 + 3 * (isolatedSupports T).card ≤ 3 * D.card := by
    exact_mod_cast hn
  rw [hcard] at hq
  linarith

#print axioms forest_budget
#print axioms charge_edges
#print axioms degree_two_budget
#print axioms conjecture365_strengthened
#print axioms conjecture365
end WOWII365Proof

