import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Finite independent-set foundations for WOWII 412d

Source: Jonas J. Gebendorfer, 11 October 2026, Sections 2--3.
This file proves only the declarations below, not the total-domination bound.
The bipartite criticality argument uses two mixed independent sets directly.
-/
namespace WOWII412dCore
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def Independent (I : Finset V) : Prop := ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v

def Maximum (I : Finset V) : Prop :=
  Independent G I ∧ ∀ J : Finset V, Independent G J → J.card ≤ I.card

noncomputable def neighbors (I : Finset V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ u ∈ I, G.Adj u v

noncomputable def difference (I : Finset V) : ℤ :=
  (I.card : ℤ) - (neighbors G I).card

def Critical (I : Finset V) : Prop :=
  Independent G I ∧ ∀ J : Finset V, Independent G J → difference G J ≤ difference G I

def MaximumCritical (I : Finset V) : Prop :=
  Critical G I ∧ ∀ J : Finset V, Critical G J → J.card ≤ I.card

noncomputable def corona : Finset V := by
  classical
  exact univ.filter fun v => ∃ I : Finset V, Maximum G I ∧ v ∈ I

noncomputable def core : Finset V := by
  classical
  exact univ.filter fun v => ∀ I : Finset V, Maximum G I → v ∈ I

noncomputable def criticalUnion : Finset V := by
  classical
  exact univ.filter fun v => ∃ I : Finset V, MaximumCritical G I ∧ v ∈ I

omit [Fintype V] [DecidableEq V] in
lemma independent_iff (I : Finset V) :
    Independent G I ↔ G.IsIndepSet (I : Set V) := by
  constructor
  · intro h u hu v hv _
    exact h u hu v hv
  · intro h u hu v hv ha
    exact h hu hv ha.ne ha

omit [DecidableEq V] in
lemma exists_maximum : ∃ I : Finset V, Maximum G I := by
  classical
  let F := (univ : Finset (Finset V)).filter (Independent G)
  have hF : F.Nonempty := ⟨∅, by simp [F, Independent]⟩
  obtain ⟨I, hI, hm⟩ := exists_max_image F Finset.card hF
  exact ⟨I, (mem_filter.mp hI).2, fun J hJ => hm J (by simp [F, hJ])⟩

lemma maximum_neighbors (I : Finset V) (hI : Maximum G I) :
    neighbors G I = univ \ I := by
  classical
  ext v
  simp only [neighbors, mem_filter, mem_univ, true_and, mem_sdiff]
  constructor
  · rintro ⟨u, hu, huv⟩
    exact fun hv => hI.1 u hu v hv huv
  · intro hv
    by_contra hn
    have hni : Independent G (insert v I) := by
      intro a ha b hb hab
      simp only [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact hab.ne rfl
      · exact hn ⟨b, hb, hab.symm⟩
      · exact hn ⟨a, ha, hab⟩
      · exact hI.1 a ha b hb hab
    have := hI.2 (insert v I) hni
    rw [card_insert_of_notMem hv] at this
    omega

omit [DecidableEq V] in
lemma independent_disjoint_neighbors (I : Finset V) (hI : Independent G I) :
    Disjoint I (neighbors G I) := by
  classical
  rw [disjoint_left]
  intro v hv hn
  obtain ⟨u, hu, huv⟩ := (mem_filter.mp hn).2
  exact hI u hu v hv huv

lemma maximum_difference (I : Finset V) (hI : Maximum G I) :
    difference G I = 2 * (I.card : ℤ) - Fintype.card V := by
  classical
  rw [difference, maximum_neighbors G I hI]
  have hc := card_sdiff_add_card_eq_card (subset_univ I)
  rw [card_univ] at hc
  omega

/-- A bipartition is represented by one independent part and its independent complement. -/
def Bipartition (A : Finset V) : Prop :=
  Independent G A ∧ Independent G (univ \ A)

lemma mixed_independent (A X : Finset V) (hA : Bipartition G A) :
    Independent G ((X ∩ A) ∪ ((univ \ A) \ neighbors G X)) := by
  classical
  intro u hu v hv huv
  simp only [mem_union, mem_inter, mem_sdiff, mem_univ, true_and] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact hA.1 u hu.2 v hv.2 huv
  · exact hv.2 (by simp [neighbors]; exact ⟨u, hu.1, huv⟩)
  · exact hu.2 (by simp [neighbors]; exact ⟨v, hv.1, huv.symm⟩)
  · exact hA.2 u (by simp [hu.1]) v (by simp [hv.1]) huv

/-- The critical-difference upper bound follows directly from two mixed independent sets. -/
lemma difference_le_maximum (A I X : Finset V) (hA : Bipartition G A)
    (hI : Maximum G I) (hX : Independent G X) :
    difference G X ≤ difference G I := by
  classical
  let C := univ \ A
  let J := (X ∩ A) ∪ (C \ neighbors G X)
  let K := (X ∩ C) ∪ (A \ neighbors G X)
  have hC : Bipartition G C := by
    dsimp [Bipartition, C]
    simpa using And.intro hA.2 hA.1
  have hJ := hI.2 J (mixed_independent G A X hA)
  have hK : Independent G K := by
    simpa [K, C] using mixed_independent G C X hC
  have hk := hI.2 K hK
  have hxn : ∀ v ∈ X, v ∉ neighbors G X := by
    intro v hv
    exact disjoint_left.mp (independent_disjoint_neighbors G X hX) hv
  have hu : J ∪ K = univ \ neighbors G X := by
    ext v
    simp only [J, K, C, mem_union, mem_inter, mem_sdiff, mem_univ, true_and]
    by_cases hv : v ∈ X <;> by_cases ha : v ∈ A <;> simp_all
  have hi : J ∩ K = X := by
    ext v
    simp only [J, K, C, mem_union, mem_inter, mem_sdiff, mem_univ, true_and]
    by_cases hv : v ∈ X <;> by_cases ha : v ∈ A <;> simp_all
  have hc := card_union_add_card_inter J K
  rw [hu, hi] at hc
  have hn := card_sdiff_add_card_eq_card (subset_univ (neighbors G X))
  rw [card_univ] at hn
  rw [difference, maximum_difference G I hI]
  omega

lemma maximum_critical (A I : Finset V) (hA : Bipartition G A) (hI : Maximum G I) :
    Critical G I :=
  ⟨hI.1, fun X hX => difference_le_maximum G A I X hA hI hX⟩

lemma maximumCritical_iff_maximum (A I : Finset V) (hA : Bipartition G A) :
    MaximumCritical G I ↔ Maximum G I := by
  constructor
  · intro hI
    obtain ⟨J, hJ⟩ := exists_maximum G
    exact ⟨hI.1.1, fun X hX => (hJ.2 X hX).trans (hI.2 J (maximum_critical G A J hA hJ))⟩
  · intro hI
    exact ⟨maximum_critical G A I hA hI, fun J hJ => hI.2 J hJ.1⟩

lemma criticalUnion_eq_corona (A : Finset V) (hA : Bipartition G A) :
    criticalUnion G = corona G := by
  classical
  ext v
  simp [criticalUnion, corona, maximumCritical_iff_maximum G A _ hA]

lemma core_subset_maximum (I : Finset V) (hI : Maximum G I) : core G ⊆ I := by
  classical
  intro v hv
  exact (mem_filter.mp hv).2 I hI

lemma maximum_subset_corona (I : Finset V) (hI : Maximum G I) : I ⊆ corona G := by
  classical
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, I, hI, hv⟩

lemma core_subset_corona : core G ⊆ corona G := by
  obtain ⟨I, hI⟩ := exists_maximum G
  exact (core_subset_maximum G I hI).trans (maximum_subset_corona G I hI)

lemma neighbors_core_disjoint_corona : Disjoint (neighbors G (core G)) (corona G) := by
  classical
  rw [disjoint_left]
  intro v hv hc
  obtain ⟨u, hu, huv⟩ := (mem_filter.mp hv).2
  obtain ⟨I, hI, hi⟩ := (mem_filter.mp hc).2
  exact hI.1 u (core_subset_maximum G I hI hu) v hi huv

/-- Every vertex in corona minus core has a neighbor in that same set.
This step needs neither bipartiteness nor a matching theorem. -/
lemma remainder_has_neighbor (v : V) (hv : v ∈ corona G \ core G) :
    ∃ w ∈ corona G \ core G, G.Adj v w := by
  classical
  have hvc := (mem_sdiff.mp hv).1
  have hvf := (mem_sdiff.mp hv).2
  have hnot : ¬ ∀ I : Finset V, Maximum G I → v ∈ I := by
    simpa [core] using hvf
  push Not at hnot
  obtain ⟨I, hI, hvi⟩ := hnot
  have hvn : v ∈ neighbors G I := by rw [maximum_neighbors G I hI]; simp [hvi]
  obtain ⟨w, hw, hwv⟩ := (mem_filter.mp hvn).2
  have hwc := maximum_subset_corona G I hI hw
  have hwf : w ∉ core G := by
    intro hh
    exact disjoint_left.mp (neighbors_core_disjoint_corona G)
      (by simp [neighbors]; exact ⟨w, hh, hwv⟩) hvc
  exact ⟨w, mem_sdiff.mpr ⟨hwc, hwf⟩, hwv.symm⟩

def joinPart (A I J : Finset V) : Finset V :=
  ((I ∩ A) ∪ (J ∩ A)) ∪ ((I \ A) ∩ (J \ A))

def meetPart (A I J : Finset V) : Finset V :=
  ((I ∩ A) ∩ (J ∩ A)) ∪ ((I \ A) ∪ (J \ A))

lemma joinPart_independent (A I J : Finset V) (hA : Bipartition G A)
    (hI : Independent G I) (hJ : Independent G J) :
    Independent G (joinPart A I J) := by
  intro u hu v hv huv
  simp only [joinPart, mem_union, mem_inter, mem_sdiff] at hu hv
  by_cases hua : u ∈ A <;> by_cases hva : v ∈ A
  · exact hA.1 u hua v hva huv
  · rcases hu with hu | hu
    · rcases hu with hu | hu
      · exact hI u hu.1 v (by tauto) huv
      · exact hJ u hu.1 v (by tauto) huv
    · tauto
  · rcases hv with hv | hv
    · rcases hv with hv | hv
      · exact hI u (by tauto) v hv.1 huv
      · exact hJ u (by tauto) v hv.1 huv
    · tauto
  · exact hA.2 u (by simp [hua]) v (by simp [hva]) huv

lemma meetPart_independent (A I J : Finset V) (hA : Bipartition G A)
    (hI : Independent G I) (hJ : Independent G J) :
    Independent G (meetPart A I J) := by
  have hc : Bipartition G (univ \ A) := by
    simpa [Bipartition] using And.intro hA.2 hA.1
  have he : meetPart A I J = joinPart (univ \ A) I J := by
    ext v
    simp [meetPart, joinPart]
    tauto
  rw [he]
  exact joinPart_independent G _ I J hc hI hJ

omit [Fintype V] in
lemma lattice_card (A I J : Finset V) :
    (joinPart A I J).card + (meetPart A I J).card = I.card + J.card := by
  have hu : joinPart A I J ∪ meetPart A I J = I ∪ J := by
    ext v
    simp only [joinPart, meetPart, mem_union, mem_inter, mem_sdiff]
    tauto
  have hi : joinPart A I J ∩ meetPart A I J = I ∩ J := by
    ext v
    simp only [joinPart, meetPart, mem_union, mem_inter, mem_sdiff]
    tauto
  have hc := card_union_add_card_inter (joinPart A I J) (meetPart A I J)
  rw [hu, hi, card_union_add_card_inter] at hc
  exact hc.symm

lemma lattice_maximum (A I J : Finset V) (hA : Bipartition G A)
    (hI : Maximum G I) (hJ : Maximum G J) :
    Maximum G (joinPart A I J) ∧ Maximum G (meetPart A I J) := by
  have hi := joinPart_independent G A I J hA hI.1 hJ.1
  have hj := meetPart_independent G A I J hA hI.1 hJ.1
  have he := lattice_card A I J
  have h1 := hI.2 _ hi
  have h2 := hI.2 _ hj
  have h3 := hJ.2 _ hI.1
  have h4 := hI.2 _ hJ.1
  have e1 : I.card = (joinPart A I J).card := by omega
  have e2 : I.card = (meetPart A I J).card := by omega
  exact ⟨⟨hi, fun K hK => e1 ▸ hI.2 K hK⟩,
    ⟨hj, fun K hK => e2 ▸ hI.2 K hK⟩⟩

/-- An extremal maximum independent set contains the entire A-side of the corona
and precisely the complement-side of the core. -/
lemma exists_extreme (A : Finset V) (hA : Bipartition G A) :
    ∃ I : Finset V, Maximum G I ∧
      (∀ J : Finset V, Maximum G J → J ∩ A ⊆ I ∩ A) ∧
      (∀ J : Finset V, Maximum G J → I \ A ⊆ J \ A) := by
  classical
  let F := (univ : Finset (Finset V)).filter (Maximum G)
  have hF : F.Nonempty := by
    obtain ⟨I, hI⟩ := exists_maximum G
    exact ⟨I, by simp [F, hI]⟩
  obtain ⟨I, hi, hm⟩ := exists_max_image F (fun J => (J ∩ A).card) hF
  have hI : Maximum G I := (mem_filter.mp hi).2
  have hleft : ∀ J : Finset V, Maximum G J → J ∩ A ⊆ I ∩ A := by
    intro J hJ
    have hj := (lattice_maximum G A I J hA hI hJ).1
    have hc := hm (joinPart A I J) (by simp [F, hj])
    have hs : I ∩ A ⊆ joinPart A I J ∩ A := by
      intro v hv
      simp only [joinPart, mem_union, mem_inter, mem_sdiff] at *
      tauto
    have he := eq_of_subset_of_card_le hs hc
    intro v hv
    rw [he]
    simp only [joinPart, mem_union, mem_inter, mem_sdiff] at *
    tauto
  refine ⟨I, hI, hleft, ?_⟩
  intro J hJ
  have hs : joinPart A I J ⊆ I := by
    intro v hv
    simp only [joinPart, mem_union, mem_inter, mem_sdiff] at hv
    rcases hv with (hv | hv) | hv
    · exact hv.1
    · exact (mem_inter.mp (hleft J hJ (mem_inter.mpr hv))).1
    · exact hv.1.1
  have hj := (lattice_maximum G A I J hA hI hJ).1
  have he := eq_of_subset_of_card_le hs (hj.2 I hI.1)
  intro v hv
  have hvi : v ∈ joinPart A I J := by rw [he]; exact (mem_sdiff.mp hv).1
  simp only [joinPart, mem_union, mem_inter, mem_sdiff] at hvi hv ⊢
  tauto

lemma extreme_eq (A I : Finset V) (hI : Maximum G I)
    (hl : ∀ J : Finset V, Maximum G J → J ∩ A ⊆ I ∩ A)
    (hr : ∀ J : Finset V, Maximum G J → I \ A ⊆ J \ A) :
    I = (corona G ∩ A) ∪ (core G \ A) := by
  classical
  ext v
  simp only [mem_union, mem_inter, mem_sdiff]
  constructor
  · intro hv
    by_cases ha : v ∈ A
    · exact Or.inl ⟨maximum_subset_corona G I hI hv, ha⟩
    · right
      refine ⟨?_, ha⟩
      simp only [core, mem_filter, mem_univ, true_and]
      intro J hJ
      exact (mem_sdiff.mp (hr J hJ (mem_sdiff.mpr ⟨hv, ha⟩))).1
  · rintro (⟨hv, ha⟩ | ⟨hv, _⟩)
    · obtain ⟨J, hJ, hj⟩ := (mem_filter.mp hv).2
      exact (mem_inter.mp (hl J hJ (mem_inter.mpr ⟨hj, ha⟩))).1
    · exact core_subset_maximum G I hI hv

/-- In a bipartite graph the excluded vertices are exactly the neighbors of the core. -/
lemma neighbors_core_eq (A : Finset V) (hA : Bipartition G A) :
    neighbors G (core G) = univ \ corona G := by
  classical
  apply Subset.antisymm
  · intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _,
      fun hc => disjoint_left.mp (neighbors_core_disjoint_corona G) hv hc⟩
  · intro v hv
    have hvc := (mem_sdiff.mp hv).2
    obtain ⟨I, hI, hl, hr⟩ := exists_extreme G A hA
    obtain ⟨J, hJ, hlj, hrj⟩ := exists_extreme G (univ \ A)
      (by simpa [Bipartition] using And.intro hA.2 hA.1)
    have hvI : v ∉ I := fun hh => hvc (maximum_subset_corona G I hI hh)
    have hvJ : v ∉ J := fun hh => hvc (maximum_subset_corona G J hJ hh)
    by_cases hva : v ∈ A
    · have hvn : v ∈ neighbors G I := by rw [maximum_neighbors G I hI]; simp [hvI]
      obtain ⟨w, hw, hwv⟩ := (mem_filter.mp hvn).2
      have hwa : w ∉ A := fun hh => hA.1 w hh v hva hwv
      have he := extreme_eq G A I hI hl hr
      rw [he] at hw
      have hwf : w ∈ core G := by simpa [hwa] using hw
      simp only [neighbors, mem_filter, mem_univ, true_and]
      exact ⟨w, hwf, hwv⟩
    · have hvn : v ∈ neighbors G J := by rw [maximum_neighbors G J hJ]; simp [hvJ]
      obtain ⟨w, hw, hwv⟩ := (mem_filter.mp hvn).2
      have hwa : w ∈ A := by
        by_contra hn
        exact hA.2 w (by simp [hn]) v (by simp [hva]) hwv
      have he := extreme_eq G (univ \ A) J hJ hlj hrj
      rw [he] at hw
      have hwf : w ∈ core G := by simpa [hwa] using hw
      simp only [neighbors, mem_filter, mem_univ, true_and]
      exact ⟨w, hwf, hwv⟩

lemma strict_neighbors_part (A X : Finset V) (hA : Bipartition G A)
    (hX : X ⊆ univ \ corona G) (hXA : X ⊆ A) (hne : X.Nonempty) :
    X.card + 1 ≤ (neighbors G X ∩ core G).card := by
  classical
  obtain ⟨I, hI, hl, hr⟩ := exists_extreme G A hA
  let Y := neighbors G X ∩ core G
  let K := (I \ Y) ∪ X
  have hYI : Y ⊆ I := fun _ hv => core_subset_maximum G I hI (mem_inter.mp hv).2
  have hXI : Disjoint X I := by
    rw [disjoint_left]
    intro v hv hi
    exact (mem_sdiff.mp (hX hv)).2 (maximum_subset_corona G I hI hi)
  have hcross : ∀ u ∈ I \ Y, ∀ v ∈ X, ¬ G.Adj u v := by
    intro u hu v hv huv
    have hua : u ∉ A := fun ha => hA.1 u ha v (hXA hv) huv
    have hui := (mem_sdiff.mp hu).1
    rw [extreme_eq G A I hI hl hr] at hui
    have huf : u ∈ core G := by simpa [hua] using hui
    have hun : u ∈ neighbors G X := by
      simp only [neighbors, mem_filter, mem_univ, true_and]
      exact ⟨v, hv, huv.symm⟩
    exact (mem_sdiff.mp hu).2 (mem_inter.mpr ⟨hun, huf⟩)
  have hk : Independent G K := by
    intro u hu v hv huv
    rcases mem_union.mp hu with hu | hu <;> rcases mem_union.mp hv with hv | hv
    · exact hI.1 u (mem_sdiff.mp hu).1 v (mem_sdiff.mp hv).1 huv
    · exact hcross u hu v hv huv
    · exact hcross v hv u hu huv.symm
    · exact hA.1 u (hXA hu) v (hXA hv) huv
  have hd : Disjoint (I \ Y) X := by
    rw [disjoint_left]
    intro v hv hx
    exact disjoint_left.mp hXI hx (mem_sdiff.mp hv).1
  have hc : K.card = (I \ Y).card + X.card := card_union_of_disjoint hd
  have hy := card_sdiff_add_card_eq_card hYI
  by_contra hn
  change ¬ X.card + 1 ≤ Y.card at hn
  have hle : I.card ≤ K.card := by omega
  have hm : Maximum G K := ⟨hk, fun J hJ => (hI.2 J hJ).trans hle⟩
  obtain ⟨v, hv⟩ := hne
  exact (mem_sdiff.mp (hX hv)).2
    (maximum_subset_corona G K hm (mem_union_right _ hv))

lemma neighbors_union (X Y : Finset V) :
    neighbors G (X ∪ Y) = neighbors G X ∪ neighbors G Y := by
  classical
  ext v
  simp [neighbors, or_and_right, exists_or]

/-- The full strict Hall inequality on the excluded vertices. -/
lemma strict_neighbors (A X : Finset V) (hA : Bipartition G A)
    (hX : X ⊆ univ \ corona G) (hne : X.Nonempty) :
    X.card + 1 ≤ (neighbors G X ∩ core G).card := by
  classical
  let L := X ∩ A
  let R := X \ A
  have hL : L ⊆ univ \ corona G := fun _ hv => hX (mem_inter.mp hv).1
  have hR : R ⊆ univ \ corona G := fun _ hv => hX (mem_sdiff.mp hv).1
  have hLA : L ⊆ A := inter_subset_right
  have hRA : R ⊆ univ \ A := fun _ hv => by simpa using (mem_sdiff.mp hv).2
  have hC : Bipartition G (univ \ A) := by
    simpa [Bipartition] using And.intro hA.2 hA.1
  have hsplit : L ∪ R = X := by ext v; simp [L, R]; tauto
  have hdis : Disjoint L R := by
    rw [disjoint_left]
    intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).2
  have hc : L.card + R.card = X.card := by
    rw [← card_union_of_disjoint hdis, hsplit]
  by_cases hln : L.Nonempty
  · by_cases hrn : R.Nonempty
    · have hl := strict_neighbors_part G A L hA hL hLA hln
      have hr := strict_neighbors_part G (univ \ A) R hC hR hRA hrn
      have hdn : Disjoint (neighbors G L ∩ core G) (neighbors G R ∩ core G) := by
        rw [disjoint_left]
        intro v hv hw
        obtain ⟨u, hu, huv⟩ := (mem_filter.mp (mem_inter.mp hv).1).2
        obtain ⟨w, hw, hwv⟩ := (mem_filter.mp (mem_inter.mp hw).1).2
        have hva : v ∉ A := fun ha => hA.1 u (hLA hu) v ha huv
        exact hA.2 w (hRA hw) v (by simp [hva]) hwv
      have he : (neighbors G L ∩ core G) ∪ (neighbors G R ∩ core G) =
          neighbors G X ∩ core G := by
        rw [← union_inter_distrib_right, ← neighbors_union G, hsplit]
      have hn := card_union_of_disjoint hdn
      rw [he] at hn
      omega
    · have hre : R = ∅ := not_nonempty_iff_eq_empty.mp hrn
      have hlx : L = X := by simpa [hre] using hsplit
      simpa [hlx] using strict_neighbors_part G A L hA hL hLA hln
  · have hle : L = ∅ := not_nonempty_iff_eq_empty.mp hln
    have hrx : R = X := by simpa [hle] using hsplit
    have hrn : R.Nonempty := hrx ▸ hne
    simpa [hrx] using strict_neighbors_part G (univ \ A) R hC hR hRA hrn

#print axioms maximumCritical_iff_maximum
#print axioms criticalUnion_eq_corona
#print axioms remainder_has_neighbor
#print axioms lattice_maximum
#print axioms neighbors_core_eq
#print axioms strict_neighbors
end WOWII412dCore
