/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree
import Mathlib.Tactic

/-!
# Independent domination across a vertex cut

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization.
Written source: *Independent Domination Across a Vertex Cut and a Resolution of
WOWII Conjecture 423*, 1 September 2026, Theorem 1.1 and its source corollary.
All assertions below quantify over arbitrary finite graphs, with no order cutoff.
-/

open SimpleGraph Finset
namespace WOWII423Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The literal closed neighborhood of a vertex set. -/
noncomputable def closedNeighborhood (G : SimpleGraph V) (A : Finset V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun v => v ∈ A ∨ ∃ a ∈ A, G.Adj a v

omit [Fintype V] in
lemma indep_insert {G : SimpleGraph V} {I : Finset V} {v : V}
    (hI : G.IsIndepSet (I : Set V)) (hv : ∀ w ∈ I, ¬G.Adj v w) :
    G.IsIndepSet ((insert v I : Finset V) : Set V) := by
  intro x hx y hy hxy
  simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact (hxy rfl).elim
  · exact hv y hy
  · exact fun h => hv x hx h.symm
  · exact hI hx hy hxy

omit [Fintype V] in
/-- Extend an independent seed inside a prescribed finite region, and dominate that region. -/
lemma extend_inside (G : SimpleGraph V) (B seed : Finset V)
    (hsB : seed ⊆ B) (hs : G.IsIndepSet (seed : Set V)) :
    ∃ I : Finset V, seed ⊆ I ∧ I ⊆ B ∧ G.IsIndepSet (I : Set V) ∧
      ∀ v ∈ B, v ∈ I ∨ ∃ w ∈ I, G.Adj v w := by
  classical
  let family := B.powerset.filter fun I => seed ⊆ I ∧ G.IsIndepSet (I : Set V)
  have hseed : seed ∈ family := by simp [family, hsB, hs]
  obtain ⟨I, hIf, hmax⟩ := family.exists_max_image Finset.card ⟨seed, hseed⟩
  have hIB : I ⊆ B := (Finset.mem_powerset.mp (Finset.mem_filter.mp hIf).1)
  have hparts := (Finset.mem_filter.mp hIf).2
  refine ⟨I, hparts.1, hIB, hparts.2, ?_⟩
  intro v hvB
  by_cases hvI : v ∈ I
  · exact Or.inl hvI
  · right
    by_contra h
    have hnon : ∀ w ∈ I, ¬G.Adj v w := by simpa only [not_exists, not_and] using h
    have hins : insert v I ∈ family := by
      simp only [family, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset_iff.mpr ⟨hvB, hIB⟩,
        hparts.1.trans (Finset.subset_insert _ _), indep_insert hparts.2 hnon⟩
    have := hmax (insert v I) hins
    rw [Finset.card_insert_of_notMem hvI] at this
    omega

/-- Independence-number bound in an induced graph, with cardinality preserved explicitly. -/
lemma card_le_induced_indepNum (G : SimpleGraph V) {I B : Finset V}
    (hIB : I ⊆ B) (hI : G.IsIndepSet (I : Set V)) :
    I.card ≤ (G.induce (B : Set V)).indepNum := by
  classical
  let f : {v // v ∈ I} → {v // v ∈ (B : Set V)} := fun v => ⟨v, hIB v.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {v // v ∈ (B : Set V)} => z.val) h)
  let T := I.attach.image f
  have hind : (G.induce (B : Set V)).IsIndepSet (T : Set {v // v ∈ (B : Set V)}) := by
    intro x hx y hy hxy
    obtain ⟨x', _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', _, rfl⟩ := Finset.mem_image.mp hy
    exact hI x'.property y'.property (fun h => hxy (Subtype.ext h))
  have hc : T.card = I.card := by
    simp only [T, Finset.card_image_of_injective _ hf, Finset.card_attach]
  simpa only [hc] using hind.card_le_indepNum

omit [Fintype V] [DecidableEq V] in
lemma indepDominationNumber_le_card (G : SimpleGraph V) {D : Finset V}
    (hD : G.IsIndepDominating (D : Set V)) : G.indepDominationNumber ≤ D.card := by
  exact csInf_le (OrderBot.bddBelow _) ⟨D, hD.1, hD.2, rfl⟩

/-- The constructive cut theorem; the `+ 1` form avoids truncated subtraction. -/
theorem cut_bound (G : SimpleGraph V) (A : Finset V) {a b : V}
    (ha : a ∈ A) (hb : b ∉ A) (hab : G.Adj a b) :
    G.indepDominationNumber + 1 ≤
      (G.induce (closedNeighborhood G A : Set V)).indepNum +
      (G.induce ((Finset.univ \ A : Finset V) : Set V)).indepNum := by
  classical
  let B := Finset.univ \ A
  have hbB : b ∈ B := by simp [B, hb]
  have hseed : G.IsIndepSet ({b} : Set V) := by
    intro x hx y hy hxy
    simp only [Set.mem_singleton_iff] at hx hy
    exact (hxy (hx.trans hy.symm)).elim
  obtain ⟨I, hbi, hIB, hI, hIdom⟩ :=
    extend_inside G B {b} (by simpa only [Finset.singleton_subset_iff] using hbB) (by simp_all)
  have hbI : b ∈ I := hbi (Finset.mem_singleton_self _)
  let U := A.filter fun v => ∀ w ∈ I, ¬G.Adj v w
  obtain ⟨J, _, hJU, hJ, hJdom⟩ := extend_inside G U ∅ (by simp) (by simp)
  have hJA : J ⊆ A := hJU.trans (Finset.filter_subset _ _)
  have hcross : ∀ v ∈ J, ∀ w ∈ I, ¬G.Adj v w := by
    intro v hv
    exact (Finset.mem_filter.mp (hJU hv)).2
  have hdis : Disjoint I J := by
    apply Finset.disjoint_left.mpr
    intro v hvI hvJ
    exact (Finset.mem_sdiff.mp (hIB hvI)).2 (hJA hvJ)
  have hDind : G.IsIndepSet ((I ∪ J : Finset V) : Set V) := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact hI hx hy hxy
    · exact fun h => hcross y hy x hx h.symm
    · exact hcross x hx y hy
    · exact hJ hx hy hxy
  have hDdom : G.IsDominating ((I ∪ J : Finset V) : Set V) := by
    intro v
    by_cases hvA : v ∈ A
    · by_cases hvU : v ∈ U
      · rcases hJdom v hvU with hv | ⟨w, hw, hvw⟩
        · exact Or.inl (Finset.mem_union_right _ hv)
        · exact Or.inr ⟨w, Finset.mem_union_right _ hw, hvw⟩
      · have : ∃ w ∈ I, G.Adj v w := by
          by_contra h
          exact hvU (Finset.mem_filter.mpr ⟨hvA, fun w hw hvw => h ⟨w, hw, hvw⟩⟩)
        obtain ⟨w, hw, hvw⟩ := this
        exact Or.inr ⟨w, Finset.mem_union_left _ hw, hvw⟩
    · rcases hIdom v (by simp [B, hvA]) with hv | ⟨w, hw, hvw⟩
      · exact Or.inl (Finset.mem_union_left _ hv)
      · exact Or.inr ⟨w, Finset.mem_union_left _ hw, hvw⟩
  have hleftind : G.IsIndepSet ((insert b J : Finset V) : Set V) :=
    indep_insert hJ (fun w hw h => hcross w hw b hbI h.symm)
  have hleftsub : insert b J ⊆ closedNeighborhood G A := by
    intro v hv
    simp only [closedNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inr ⟨a, ha, hab⟩
    · exact Or.inl (hJA hv)
  have hbJ : b ∉ J := fun h => hb (hJA h)
  have hx := card_le_induced_indepNum G hleftsub hleftind
  rw [Finset.card_insert_of_notMem hbJ] at hx
  have hy := card_le_induced_indepNum G hIB hI
  have hi := indepDominationNumber_le_card G ⟨hDind, hDdom⟩
  rw [Finset.card_union_of_disjoint hdis] at hi
  dsimp only [B] at hy
  omega

/-- The additive bound implies the product bound for any nonempty proper cut. -/
theorem product_cut_bound (G : SimpleGraph V) (hG : G.Connected) (A : Finset V)
    (hne : A.Nonempty) (hproper : A ≠ Finset.univ) :
    G.indepDominationNumber ≤
      (G.induce (closedNeighborhood G A : Set V)).indepNum *
      (G.induce ((Finset.univ \ A : Finset V) : Set V)).indepNum := by
  classical
  obtain ⟨b, hb, a, ha, hba⟩ := hG.exists_adj_finset_compl hne hproper
  have hcut := cut_bound G A ha hb hba.symm
  have hx : 1 ≤ (G.induce (closedNeighborhood G A : Set V)).indepNum := by
    have hsub : {a} ⊆ closedNeighborhood G A := by
      simp only [Finset.singleton_subset_iff, closedNeighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact Or.inl ha
    have hind : G.IsIndepSet (({a} : Finset V) : Set V) := by simp
    simpa using card_le_induced_indepNum G hsub hind
  have hy : 1 ≤ (G.induce ((Finset.univ \ A : Finset V) : Set V)).indepNum := by
    have hsub : {b} ⊆ Finset.univ \ A := by simp [hb]
    have hind : G.IsIndepSet (({b} : Finset V) : Set V) := by simp
    simpa using card_le_induced_indepNum G hsub hind
  nlinarith

/-- A connected graph with at least two vertices has an independent dominating
set of size at most its edge count. This supplies the regular branch of 423. -/
lemma indepDominationNumber_le_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hn : 1 < Fintype.card V) :
    G.indepDominationNumber ≤ G.edgeFinset.card := by
  classical
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨a⟩ := (inferInstance : Nonempty V)
  have hsingle : ({a} : Finset V) ≠ Finset.univ := by
    intro h
    have := congrArg Finset.card h
    simp only [Finset.card_singleton, Finset.card_univ] at this
    omega
  obtain ⟨b, _, a', _, hba⟩ :=
    hG.exists_adj_finset_compl (Finset.singleton_nonempty a) hsingle
  obtain ⟨D, _, _, hind, hdom⟩ := extend_inside G Finset.univ ∅ (by simp) (by simp)
  have hDne : D ≠ Finset.univ := by
    intro h
    have hbD : b ∈ D := by rw [h]; exact Finset.mem_univ _
    have haD : a' ∈ D := by rw [h]; exact Finset.mem_univ _
    exact hind hbD haD hba.ne hba
  have hcard := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ D, hDne⟩)
  have hi := indepDominationNumber_le_card G ⟨hind, fun v => hdom v (Finset.mem_univ v)⟩
  have he := hG.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← G.edgeFinset_card] at he
  simp only [Finset.card_univ] at hcard
  omega

/-- WOWII 423, using the recovered non-strict upper-bound reading of its
missing HTML comparison glyph. `internalEdges` counts induced edges exactly. -/
theorem conjecture423 (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hn : 3 < Fintype.card V) :
    let A := Finset.univ.filter fun v => G.degree v = G.minDegree
    let M := Finset.univ.filter fun v => G.degree v = G.maxDegree
    G.indepDominationNumber ≤ (G.internalEdges M).card +
      (G.induce (closedNeighborhood G A : Set V)).indepNum *
      (G.induce ((Finset.univ \ A : Finset V) : Set V)).indepNum := by
  classical
  dsimp only
  let A := Finset.univ.filter fun v => G.degree v = G.minDegree
  let M := Finset.univ.filter fun v => G.degree v = G.maxDegree
  change G.indepDominationNumber ≤ (G.internalEdges M).card +
    (G.induce (closedNeighborhood G A : Set V)).indepNum *
    (G.induce ((Finset.univ \ A : Finset V) : Set V)).indepNum
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  by_cases hA : A = Finset.univ
  · have hdeg : ∀ v, G.degree v = G.minDegree := by
      intro v
      have : v ∈ A := by rw [hA]; exact Finset.mem_univ _
      exact (Finset.mem_filter.mp this).2
    have hmax : G.maxDegree = G.minDegree :=
      Nat.le_antisymm (G.maxDegree_le_of_forall_degree_le _ (fun v => (hdeg v).le))
        G.minDegree_le_maxDegree
    have hM : M = Finset.univ := by
      ext v
      simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hmax]
      exact iff_of_true (hdeg v) trivial
    have heq : G.internalEdges M = G.edgeFinset := by
      simp [hM, SimpleGraph.internalEdges]
    have hi := indepDominationNumber_le_edges G hG (by omega)
    rw [heq]
    omega
  · have hne : A.Nonempty := by
      obtain ⟨a, ha⟩ := G.exists_minimal_degree_vertex
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm⟩⟩
    have hi := product_cut_bound G hG A hne hA
    omega

end WOWII423Proof
