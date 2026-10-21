import FormalConjectures.WrittenOnTheWallII.GraphConjecture348

/-!
A finite rooted description of an actual simple tree, used to telescope local
integer potentials. No recursively substituted graph invariant is introduced.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Finset SimpleGraph

namespace WOWIIRootedFlow

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma exists_parent (hc : G.Connected) (r : V) :
    ∃ p : V → V, p r = r ∧ ∀ v, v ≠ r →
      G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r := by
  classical
  have hex : ∀ v, ∃ w, (v = r → w = r) ∧
      (v ≠ r → G.Adj v w ∧ G.dist w r + 1 = G.dist v r) := by
    intro v
    by_cases hv : v = r
    · exact ⟨r, fun _ => rfl, fun h => (h hv).elim⟩
    obtain ⟨walk, hlen⟩ := hc.exists_walk_length_eq_dist v r
    cases walk with
    | nil => exact (hv rfl).elim
    | @cons v w r hadj tail =>
      refine ⟨w, fun h => (hv h).elim, fun _ => ⟨hadj, ?_⟩⟩
      have htail := G.dist_le tail
      have htri := hadj.reachable.dist_triangle_left r
      rw [G.dist_eq_one_iff_adj.mpr hadj] at htri
      simp only [Walk.length_cons] at hlen
      omega
  choose p hp using hex
  exact ⟨p, (hp r).1 rfl, fun v hv => (hp v).2 hv⟩

def children (p : V → V) (r v : V) : Finset V :=
  Finset.univ.filter fun w => w ≠ r ∧ p w = v

lemma parent_classification (hT : G.IsTree) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r) :
    ∀ v w, G.Adj v w ↔ (v ≠ r ∧ p v = w) ∨ (w ≠ r ∧ p w = v) := by
  classical
  let S := (Finset.univ : Finset V).erase r
  let E := S.image fun v => s(v, p v)
  have hinj : Set.InjOn (fun v => s(v, p v)) (S : Set V) := by
    intro v hv w hw he
    rcases Sym2.eq_iff.mp he with he | he
    · exact he.1
    · have hvp := (hp v (Finset.mem_erase.mp hv).1).2
      have hwp := (hp w (Finset.mem_erase.mp hw).1).2
      rw [he.2] at hvp
      rw [← he.1] at hwp
      omega
  have hcardE : E.card = S.card := Finset.card_image_of_injOn hinj
  have hsub : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    simpa using (hp v (Finset.mem_erase.mp hv).1).1
  have hcardS : S.card + 1 = Fintype.card V := by
    simpa [S] using Finset.card_erase_add_one (Finset.mem_univ r)
  have ht := hT.card_edgeFinset
  have hEq : E = G.edgeFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro v w
  constructor
  · intro hadj
    have he : s(v, w) ∈ E := by rw [hEq]; simpa using hadj
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp he
    rcases Sym2.eq_iff.mp heq with heq | heq
    · obtain ⟨rfl, he⟩ := heq
      exact Or.inl ⟨(Finset.mem_erase.mp hu).1, he⟩
    · obtain ⟨rfl, he⟩ := heq
      exact Or.inr ⟨(Finset.mem_erase.mp hu).1, he⟩
  · rintro (⟨hv, rfl⟩ | ⟨hw, rfl⟩)
    · exact (hp v hv).1
    · exact (hp w hw).1.symm

lemma parent_not_child (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r)
    (v : V) (hv : v ≠ r) : p v ∉ children p r v := by
  intro hm
  obtain ⟨hpne, hpp⟩ := (Finset.mem_filter.mp hm).2
  have h1 := (hp v hv).2
  have h2 := (hp (p v) hpne).2
  rw [hpp] at h2
  omega

lemma degree_children (hT : G.IsTree) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r)
    (v : V) (hv : v ≠ r) : G.degree v = (children p r v).card + 1 := by
  have hclass := parent_classification G hT r p hp
  have heq : G.neighborFinset v = insert (p v) (children p r v) := by
    ext w
    simp [children, hclass, hv, eq_comm]
  have hc := congrArg Finset.card heq
  simpa [parent_not_child G r p hp v hv] using hc

lemma root_degree_children (hT : G.IsTree) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r) :
    G.degree r = (children p r r).card := by
  have hclass := parent_classification G hT r p hp
  have heq : G.neighborFinset r = children p r r := by
    ext w
    simp [children, hclass]
  exact congrArg Finset.card heq

lemma sum_children (r : V) (p : V → V) (f : V → ℤ) :
    (∑ v : V, ∑ w ∈ children p r v, f w) = ∑ w ∈ Finset.univ.erase r, f w := by
  classical
  have herase : (Finset.univ : Finset V).erase r =
      Finset.univ.filter fun w => w ≠ r := by
    ext w
    simp
  simp only [children, Finset.sum_filter]
  rw [Finset.sum_comm, herase, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : w = r
  · simp [h]
  · simp [h, eq_comm]

end WOWIIRootedFlow

namespace WOWIIRootedFlow
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def message (D : Finset V) (p : V → V) (v : V) : ℤ :=
  if G.degree v = 1 then (if v ∈ D then 3 else 0) - (if G.degree (p v) = 2 then 2 else 0)
  else if G.degree v = 2 then (if v ∈ D then (if p v ∈ D then 1 else 4) else 2)
  else if v ∈ D then (if p v ∈ D ∧ G.degree (p v) = 2 then 1 else 2) else 2

noncomputable def charge (D : Finset V) (v : V) : ℤ :=
  (if v ∈ D then 3 else 0) -
    (if v ∈ WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G then 2 else 0)

lemma message_selected (D : Finset V) (p : V → V) (v : V) (hv : v ∈ D) :
    1 ≤ message G D p v := by
  simp only [message, hv, if_true]
  split_ifs <;> omega

lemma message_degree_two (D : Finset V) (p : V → V) (v : V) (hv : G.degree v = 2) :
    1 ≤ message G D p v := by
  simp only [message, hv, OfNat.one_ne_ofNat, if_false, if_true]
  split_ifs <;> omega

lemma leaf_neighbor_eq_parent (hT : G.IsTree) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r)
    (v : V) (hv : v ≠ r) (hdeg : G.degree v = 1) :
    ∀ w, G.Adj v w → w = p v := by
  have hc := degree_children G hT r p hp v hv
  have hempty : children p r v = ∅ := Finset.card_eq_zero.mp (by omega)
  intro w hw
  rcases (parent_classification G hT r p hp v w).mp hw with ⟨_, he⟩ | ⟨hw, he⟩
  · exact he.symm
  · have hm : w ∈ children p r v := by simp [children, hw, he]
    simp [hempty] at hm

lemma leaf_parent_selected (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r)
    (v : V) (hv : v ≠ r) (hdeg : G.degree v = 1) : p v ∈ D := by
  obtain ⟨w, hw, hadj⟩ := hD v
  have he := leaf_neighbor_eq_parent G hT r p hp v hv hdeg w hadj
  exact he ▸ hw

lemma message_parent_not_selected (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r)
    (v : V) (hv : v ≠ r) (hn : p v ∉ D) : 2 ≤ message G D p v := by
  have hleaf : G.degree v ≠ 1 := fun h => hn (leaf_parent_selected G hT D hD r p hp v hv h)
  simp only [message, hleaf, hn, false_and, if_false]
  split_ifs <;> omega

lemma message_parent_not_two (D : Finset V) (p : V → V) (v : V)
    (hp : p v ∈ D) (hq : G.degree (p v) ≠ 2) : 0 ≤ message G D p v := by
  simp only [message, hp, hq, true_and, if_true, if_false]
  split_ifs <;> omega

lemma message_lower (D : Finset V) (p : V → V) (v : V) :
    -2 ≤ message G D p v := by
  simp only [message]
  split_ifs <;> omega

lemma child_sum_nonneg (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r)
    (v : V) (hv : v ∈ D) (hdeg : G.degree v ≠ 2) :
    0 ≤ ∑ w ∈ children p r v, message G D p w := by
  apply Finset.sum_nonneg
  intro w hw
  obtain ⟨_, he⟩ := (Finset.mem_filter.mp hw).2
  exact message_parent_not_two G D p w (by simpa only [he] using hv) (by simpa only [he] using hdeg)

lemma local_potential (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) (r : V) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r)
    (v : V) (hv : v ≠ r) :
    message G D p v ≤ charge G D v + ∑ w ∈ children p r v, message G D p w := by
  classical
  have hclass := parent_classification G hT r p hp
  have hdc := degree_children G hT r p hp v hv
  by_cases hleaf : G.degree v = 1
  · have hempty : children p r v = ∅ := Finset.card_eq_zero.mp (by omega)
    have hb : v ∈ WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G ↔
        G.degree (p v) = 2 := by
      simp only [WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, w, hw, hd⟩
        rwa [leaf_neighbor_eq_parent G hT r p hp v hv hleaf w hw] at hd
      · intro hq
        exact ⟨by omega, p v, (hp v hv).1, hq⟩
    simp [message, charge, hleaf, hempty, hb]
  by_cases htwo : G.degree v = 2
  · have hc : (children p r v).card = 1 := by omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc
    have hwm : w ∈ children p r v := by rw [hw]; simp
    obtain ⟨hwr, hpw⟩ := (Finset.mem_filter.mp hwm).2
    have hb : v ∉ WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G := by
      simp [WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors, htwo]
    rw [hw, Finset.sum_singleton]
    by_cases hs : v ∈ D
    · by_cases ht : p v ∈ D
      · have hlow := message_lower G D p w
        simp only [message, hleaf, htwo, hs, ht, if_false, if_true] 
        simp only [charge, hs, hb, if_true, if_false, sub_zero]
        omega
      · obtain ⟨u, hu, hadj⟩ := hD v
        have hus : u ∈ children p r v := by
          rcases (hclass v u).mp hadj with ⟨_, he⟩ | ⟨hur, he⟩
          · exact (ht (by simpa only [he] using hu)).elim
          · simp [children, hur, he]
        have hue : u = w := by simpa [hw] using hus
        have hwsel : w ∈ D := hue ▸ hu
        have hlow := message_selected G D p w hwsel
        simp only [message, hleaf, htwo, hs, ht, if_false, if_true, charge, hb, sub_zero]
        omega
    · have hlow := message_parent_not_selected G hT D hD r p hp w hwr (by simpa only [hpw] using hs)
      simp only [message, hleaf, htwo, hs, if_false, if_true, charge, hb, sub_zero]
      omega
  have hc : 2 ≤ (children p r v).card := by omega
  by_cases hs : v ∈ D
  · have hsum := child_sum_nonneg G hT D hD r p hp v hs htwo
    by_cases hpar : p v ∈ D ∧ G.degree (p v) = 2
    · simp only [message, hleaf, htwo, hs, hpar, if_false, if_true, charge]
      split_ifs <;> omega
    have hwitness : v ∈ WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G →
        1 ≤ ∑ w ∈ children p r v, message G D p w := by
      intro hb
      obtain ⟨_, w, hadj, hd⟩ := (Finset.mem_filter.mp hb).2
      have hsingle (u : V) (hu : u ∈ children p r v) (hl : 1 ≤ message G D p u) :
          1 ≤ ∑ z ∈ children p r v, message G D p z := by
        have hh : message G D p u ≤ ∑ z ∈ children p r v, message G D p z :=
          Finset.single_le_sum (fun z hz => by
            obtain ⟨_, hez⟩ := (Finset.mem_filter.mp hz).2
            exact message_parent_not_two G D p z
              (by simpa only [hez] using hs) (by simpa only [hez] using htwo)) hu
        omega
      rcases (hclass v w).mp hadj with ⟨_, he⟩ | ⟨hwr, he⟩
      · have hpdeg : G.degree (p v) = 2 := by simpa [he] using hd
        have hpnot : p v ∉ D := fun h => hpar ⟨h, hpdeg⟩
        obtain ⟨u, hu, hau⟩ := hD v
        rcases (hclass v u).mp hau with ⟨_, heu⟩ | ⟨hur, heu⟩
        · exact (hpnot (by simpa only [heu] using hu)).elim
        · exact hsingle u (by simp [children, hur, heu]) (message_selected G D p u hu)
      · exact hsingle w (by simp [children, hwr, he]) (message_degree_two G D p w hd)
    simp only [message, hleaf, htwo, hs, hpar, if_false, if_true, charge]
    split_ifs with hb
    · have := hwitness hb
      omega
    · omega
  · have hsum : 2 * (children p r v).card ≤ ∑ w ∈ children p r v, message G D p w := by
      calc
        (2 : ℤ) * (children p r v).card = ∑ _ ∈ children p r v, (2 : ℤ) := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨hwr, he⟩ := (Finset.mem_filter.mp hw).2
          exact message_parent_not_selected G hT D hD r p hp w hwr (by simpa only [he] using hs)
    have hcZ : (2 : ℤ) ≤ (children p r v).card := by exact_mod_cast hc
    simp only [message, hleaf, htwo, hs, if_false, charge]
    split_ifs <;> omega
end WOWIIRootedFlow

namespace WOWIIRootedFlow
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma neighbor_of_leaf_not_leaf (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (r v : V) (hr : G.degree r = 1) (hadj : G.Adj r v) : G.degree v ≠ 1 := by
  intro hv
  have hruniq := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hr)
  have hvuniq := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv)
  have hru (w : V) (hw : G.Adj r w) : w = v := hruniq.unique hw hadj
  have hvu (w : V) (hw : G.Adj v w) : w = r := hvuniq.unique hw hadj.symm
  let S : Finset V := {r, v}
  have hclosed : ∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S := by
    intro u hu w hw
    rcases (show u = r ∨ u = v by simpa [S] using hu) with rfl | rfl
    · simp [S, hru w hw]
    · simp [S, hvu w hw]
  have hwalk : ∀ {u w : V}, G.Walk u w → u ∈ S → w ∈ S := by
    intro u w q
    induction q with
    | nil => exact id
    | cons h tail ih => exact fun hu => ih (hclosed _ hu _ h)
  have hsub : (Finset.univ : Finset V) ⊆ S := by
    intro w _
    obtain ⟨q⟩ := hT.connected.preconnected r w
    exact hwalk q (by simp [S])
  have hc := Finset.card_le_card hsub
  have hcs : S.card ≤ 2 := by
    calc
      S.card ≤ (Finset.singleton v).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  simp only [Finset.card_univ] at hc
  omega

lemma root_potential (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (D : Finset V) (hD : G.IsTotalDominating (D : Set V))
    (r : V) (hr : G.degree r = 1) (p : V → V)
    (hp : ∀ v, v ≠ r → G.Adj v (p v) ∧ G.dist (p v) r + 1 = G.dist v r) :
    2 ≤ charge G D r + ∑ w ∈ children p r r, message G D p w := by
  have hc := root_degree_children G hT r p hp
  have hc1 : (children p r r).card = 1 := by omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc1
  have hvm : v ∈ children p r r := by rw [hv]; simp
  obtain ⟨hvr, hpv⟩ := (Finset.mem_filter.mp hvm).2
  have hadj : G.Adj r v := by simpa only [hpv] using (hp v hvr).1.symm
  have hvleaf := neighbor_of_leaf_not_leaf G hT hn r v hr hadj
  have hvsel : v ∈ D := by
    obtain ⟨w, hw, hadjw⟩ := hD r
    have he : w = v := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hr).unique hadjw hadj
    exact he ▸ hw
  have hb : r ∈ WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G ↔
      G.degree v = 2 := by
    simp only [WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, w, hw, hd⟩
      have he : w = v := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hr).unique hw hadj
      exact he ▸ hd
    · exact fun hd => ⟨by omega, v, hadj, hd⟩
  rw [hv, Finset.sum_singleton]
  simp only [charge, message, hvleaf, hvsel, hpv, hr, hb, if_false, if_true]
  split_ifs <;> omega

lemma bound_set_348 (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (D : Finset V) (hD : G.IsTotalDominating (D : Set V)) :
    2 * (WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G).card + 2 ≤
      3 * D.card := by
  classical
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨r, hr⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨p, hpr, hp⟩ := exists_parent G hT.connected r
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (f := fun v => if v = r then (2 : ℤ) else message G D p v)
    (g := fun v => charge G D v + ∑ w ∈ children p r v, message G D p w)
    (by
      intro v _
      by_cases he : v = r
      · subst v
        simpa only [if_pos rfl] using root_potential G hT hn D hD r hr p hp
      · simpa only [if_neg he] using local_potential G hT D hD r p hp v he)
  have hleft : (∑ v : V, if v = r then (2 : ℤ) else message G D p v) =
      2 + ∑ v ∈ Finset.univ.erase r, message G D p v := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
    simp only [if_pos rfl]
    have he : (∑ v ∈ Finset.univ.erase r, if v = r then (2 : ℤ) else message G D p v) =
        ∑ v ∈ Finset.univ.erase r, message G D p v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact if_neg (Finset.mem_erase.mp hv).1
    rw [he]
    omega
  rw [hleft, Finset.sum_add_distrib, sum_children] at hs
  have hc : (∑ v : V, charge G D v) =
      3 * (D.card : ℤ) -
        2 * ((WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G).card : ℤ) := by
    simp only [charge, Finset.sum_sub_distrib]
    have h3 : (∑ v : V, if v ∈ D then (3 : ℤ) else 0) = 3 * (D.card : ℤ) := by
      rw [← Finset.sum_filter]
      simp
      omega
    have h2 : (∑ v : V, if v ∈ WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G
        then (2 : ℤ) else 0) =
        2 * ((WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G).card : ℤ) := by
      rw [← Finset.sum_filter]
      simp
      omega
    rw [h3, h2]
  rw [hc] at hs
  omega

theorem positive_348 (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    2 * (WrittenOnTheWallII.GraphConjecture348.externalDegreeTwoNeighbors G).card ≤
      3 * G.totalDominationNumber := by
  classical
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hfull : G.IsTotalDominating (Finset.univ : Finset V) := by
    intro v
    have hpos : 0 < G.degree v :=
      lt_of_lt_of_le hT.preconnected.minDegree_pos_of_nontrivial (G.minDegree_le_degree v)
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    exact ⟨w, Finset.mem_univ _, by simpa using hw⟩
  have hne : {n | ∃ D : Finset V, G.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨Fintype.card V, Finset.univ, hfull, by simp⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  have hbound := bound_set_348 G hT hn D hD.isTotalDominating
  have hsize := hD.card_eq
  change D.card = G.totalDominationNumber at hsize
  rw [hsize] at hbound
  omega
end WOWIIRootedFlow
#print axioms WOWIIRootedFlow.positive_348
