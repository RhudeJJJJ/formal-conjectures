import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! Finite indexed hypergraphs for the exact total-domination proof.
Edge indices are retained, so repeated neighborhoods remain separate rows. -/

namespace TotalDominationAnnihilationProof.Hypergraph
open Finset SimpleGraph

variable {V I : Type*} [DecidableEq V]

def incident (J : Finset I) (edge : I → Finset V) (v : V) : Finset I :=
  J.filter fun i => v ∈ edge i

@[simp] theorem mem_incident {J : Finset I} {edge : I → Finset V} {v : V} {i : I} :
    i ∈ incident J edge v ↔ i ∈ J ∧ v ∈ edge i := by
  simp [incident]

def Hits (J : Finset I) (edge : I → Finset V) (D : Finset V) : Prop :=
  ∀ i ∈ J, ∃ v ∈ D, v ∈ edge i

def twoVertices (U : Finset V) (J : Finset I) (edge : I → Finset V) : Finset V :=
  U.filter fun v => (incident J edge v).card = 2

def pairGraph (U : Finset V) (J : Finset I) (edge : I → Finset V) :
    SimpleGraph ↥(twoVertices U J edge) where
  Adj x y := x ≠ y ∧ ∃ i ∈ J, x.val ∈ edge i ∧ y.val ∈ edge i
  symm := ⟨by
    rintro x y ⟨hne, i, hi, hx, hy⟩
    exact ⟨hne.symm, i, hi, hy, hx⟩⟩
  loopless := ⟨by rintro x ⟨hne, _⟩; exact hne rfl⟩

/-- Counting actual incidences, with the original edge indices retained. -/
theorem sum_incident_card (U : Finset V) (J : Finset I) (edge : I → Finset V)
    (hsub : ∀ i ∈ J, edge i ⊆ U) :
    ∑ v ∈ U, (incident J edge v).card = ∑ i ∈ J, (edge i).card := by
  simp only [incident, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  have hf : U.filter (fun v => v ∈ edge i) = edge i := by
    ext v
    simp only [mem_filter]
    exact ⟨And.right, fun hv => ⟨hsub i hi hv, hv⟩⟩
  rw [hf]

/-- Each conflict vertex is in two three-edges, so its conflict degree is at most four. -/
theorem pairGraph_degree_le_four (U : Finset V) (J : Finset I)
    (edge : I → Finset V) [DecidableRel (pairGraph U J edge).Adj]
    (hthree : ∀ i ∈ J, (edge i).card = 3)
    (x : ↥(twoVertices U J edge)) : (pairGraph U J edge).degree x ≤ 4 := by
  classical
  have hx2 : (incident J edge x.val).card = 2 := (mem_filter.mp x.property).2
  obtain ⟨a, b, hab, hinc⟩ := Finset.card_eq_two.mp hx2
  have ha : a ∈ J ∧ x.val ∈ edge a := by
    apply mem_incident.mp
    rw [hinc]
    simp
  have hb : b ∈ J ∧ x.val ∈ edge b := by
    apply mem_incident.mp
    rw [hinc]
    simp
  have hcover :
      ((pairGraph U J edge).neighborFinset x).image Subtype.val ⊆
        (edge a).erase x.val ∪ (edge b).erase x.val := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hv
    have hxy := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    obtain ⟨hne, i, hi, hxi, hyi⟩ := hxy
    have hei : i ∈ incident J edge x.val := mem_incident.mpr ⟨hi, hxi⟩
    rw [hinc] at hei
    have hyne : y.val ≠ x.val := fun h => hne (Subtype.ext h.symm)
    rcases mem_insert.mp hei with rfl | hei
    · exact mem_union_left _ (mem_erase.mpr ⟨hyne, hyi⟩)
    · have hib : i = b := by simpa only [mem_singleton] using hei
      exact mem_union_right _ (mem_erase.mpr ⟨hyne, hib ▸ hyi⟩)
  have hcard := card_le_card hcover
  rw [card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have hunion := card_union_le ((edge a).erase x.val) ((edge b).erase x.val)
  rw [card_erase_of_mem ha.2, card_erase_of_mem hb.2, hthree a ha.1,
    hthree b hb.1] at hunion
  omega

/-- A pairwise-conflicting collection of vertices of incidence degree two has
at most four members when every indexed edge has size three. -/
theorem pairwise_conflict_card_le_four (J : Finset I) (edge : I → Finset V)
    (hthree : ∀ i ∈ J, (edge i).card = 3) (S : Finset V)
    (hdeg : ∀ v ∈ S, (incident J edge v).card = 2)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i ∈ J, x ∈ edge i ∧ y ∈ edge i) :
    S.card ≤ 4 := by
  classical
  by_contra hbad
  have hSpos : 0 < S.card := by omega
  obtain ⟨x, hx⟩ := card_pos.mp hSpos
  obtain ⟨a, b, hab, hinc⟩ := card_eq_two.mp (hdeg x hx)
  have ha : a ∈ J ∧ x ∈ edge a := by
    apply mem_incident.mp
    rw [hinc]
    simp
  have hb : b ∈ J ∧ x ∈ edge b := by
    apply mem_incident.mp
    rw [hinc]
    simp
  have hSsub : S ⊆ edge a ∪ edge b := by
    intro y hy
    by_cases hyx : y = x
    · exact hyx ▸ mem_union_left _ ha.2
    obtain ⟨i, hi, hxi, hyi⟩ := hpair x hx y hy (Ne.symm hyx)
    have hii : i ∈ incident J edge x := mem_incident.mpr ⟨hi, hxi⟩
    rw [hinc] at hii
    rcases mem_insert.mp hii with rfl | hii
    · exact mem_union_left _ hyi
    · have hib : i = b := mem_singleton.mp hii
      exact mem_union_right _ (hib ▸ hyi)
  have hcount := card_union_add_card_inter (edge a) (edge b)
  rw [hthree a ha.1, hthree b hb.1] at hcount
  have hcardS := card_le_card hSsub
  have hxinter : x ∈ edge a ∩ edge b := mem_inter.mpr ⟨ha.2, hb.2⟩
  have hintpos : 0 < (edge a ∩ edge b).card := card_pos.mpr ⟨x, hxinter⟩
  have hintcard : (edge a ∩ edge b).card = 1 := by omega
  have hScard : S.card = 5 := by omega
  have hSeq : S = edge a ∪ edge b :=
    eq_of_subset_of_card_le hSsub (by omega)
  have hinter : edge a ∩ edge b = {x} := by
    obtain ⟨z, hz⟩ := card_eq_one.mp hintcard
    have hxz : x = z := by
      rw [hz] at hxinter
      exact mem_singleton.mp hxinter
    simpa only [← hxz] using hz
  let A := (edge a).erase x
  let B := (edge b).erase x
  have hAc : A.card = 2 := by simp [A, card_erase_of_mem ha.2, hthree a ha.1]
  have hBc : B.card = 2 := by simp [B, card_erase_of_mem hb.2, hthree b hb.1]
  have hAS : A ⊆ S := by
    intro v hv
    rw [hSeq]
    exact mem_union_left _ (mem_erase.mp hv).2
  have hBS : B ⊆ S := by
    intro v hv
    rw [hSeq]
    exact mem_union_right _ (mem_erase.mp hv).2
  have hAnotb : ∀ v ∈ A, v ∉ edge b := by
    intro v hv hvb
    have hvint : v ∈ edge a ∩ edge b := mem_inter.mpr ⟨(mem_erase.mp hv).2, hvb⟩
    rw [hinter] at hvint
    exact (mem_erase.mp hv).1 (mem_singleton.mp hvint)
  have hBnota : ∀ v ∈ B, v ∉ edge a := by
    intro v hv hva
    have hvint : v ∈ edge a ∩ edge b := mem_inter.mpr ⟨hva, (mem_erase.mp hv).2⟩
    rw [hinter] at hvint
    exact (mem_erase.mp hv).1 (mem_singleton.mp hvint)
  have hdis : Disjoint A B := Finset.disjoint_left.mpr fun v hvA hvB =>
    hAnotb v hvA (mem_erase.mp hvB).2
  have hne : ∀ v ∈ A, ∀ w ∈ B, v ≠ w := by
    intro v hv w hw heq
    exact Finset.disjoint_left.mp hdis hv (heq ▸ hw)
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < A.card by omega)
  obtain ⟨w, hw⟩ := card_pos.mp (show 0 < B.card by omega)
  obtain ⟨g, hg, hvg, hwg⟩ := hpair v (hAS hv) w (hBS hw) (hne v hv w hw)
  have hga : g ≠ a := by
    intro h
    exact hBnota w hw (h ▸ hwg)
  have hgb : g ≠ b := by
    intro h
    exact hAnotb v hv (h ▸ hvg)
  have hvi : incident J edge v = {a, g} := by
    symm
    apply eq_of_subset_of_card_le
    · intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact mem_incident.mpr ⟨ha.1, (mem_erase.mp hv).2⟩
      · have hig : i = g := mem_singleton.mp hi
        exact hig ▸ mem_incident.mpr ⟨hg, hvg⟩
    · rw [hdeg v (hAS hv)]
      simp [Ne.symm hga]
  have hwi : incident J edge w = {b, g} := by
    symm
    apply eq_of_subset_of_card_le
    · intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact mem_incident.mpr ⟨hb.1, (mem_erase.mp hw).2⟩
      · have hig : i = g := mem_singleton.mp hi
        exact hig ▸ mem_incident.mpr ⟨hg, hwg⟩
    · rw [hdeg w (hBS hw)]
      simp [Ne.symm hgb]
  have hBg : B ⊆ edge g := by
    intro y hy
    obtain ⟨i, hi, hvi', hyi⟩ := hpair v (hAS hv) y (hBS hy) (hne v hv y hy)
    have hii : i ∈ incident J edge v := mem_incident.mpr ⟨hi, hvi'⟩
    rw [hvi] at hii
    rcases mem_insert.mp hii with rfl | hii
    · exact False.elim (hBnota y hy hyi)
    · exact (mem_singleton.mp hii) ▸ hyi
  have hAg : A ⊆ edge g := by
    intro y hy
    obtain ⟨i, hi, hwi', hyi⟩ := hpair w (hBS hw) y (hAS hy) (Ne.symm (hne y hy w hw))
    have hii : i ∈ incident J edge w := mem_incident.mpr ⟨hi, hwi'⟩
    rw [hwi] at hii
    rcases mem_insert.mp hii with rfl | hii
    · exact False.elim (hAnotb y hy hyi)
    · exact (mem_singleton.mp hii) ▸ hyi
  have hunion : A ∪ B ⊆ edge g := union_subset hAg hBg
  have hsize := card_le_card hunion
  rw [card_union_of_disjoint hdis, hAc, hBc, hthree g hg] at hsize
  omega

/-- The conflict graph has no five-clique. -/
theorem pairGraph_cliqueFree_five (U : Finset V) (J : Finset I)
    (edge : I → Finset V) (hthree : ∀ i ∈ J, (edge i).card = 3) :
    (pairGraph U J edge).CliqueFree 5 := by
  classical
  intro S hS
  obtain ⟨hc, hcard⟩ := SimpleGraph.isNClique_iff.mp hS
  let R := S.image Subtype.val
  have hRcard : R.card = 5 := by
    rw [card_image_of_injective _ Subtype.val_injective]
    exact hcard
  have hRdeg : ∀ v ∈ R, (incident J edge v).card = 2 := by
    intro v hv
    obtain ⟨x, _, rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp x.property).2
  have hRpair : ∀ x ∈ R, ∀ y ∈ R, x ≠ y →
      ∃ i ∈ J, x ∈ edge i ∧ y ∈ edge i := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_image.mp hy
    have hne : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    exact ((SimpleGraph.isClique_iff.mp hc) hx' hy' hne).2
  have hb := pairwise_conflict_card_le_four J edge hthree R hRdeg hRpair
  omega

/-- In incidence degree at most two, a proper four-coloring supplies the exact
Chvatal--McDiarmid cover bound. The coloring is an explicit input here. -/
theorem three_cover_of_four_coloring (U : Finset V) (J : Finset I)
    (edge : I → Finset V) (hsub : ∀ i ∈ J, edge i ⊆ U)
    (hthree : ∀ i ∈ J, (edge i).card = 3)
    (hdeg : ∀ v ∈ U, (incident J edge v).card ≤ 2)
    (hcolor : (pairGraph U J edge).Colorable 4) :
    ∃ D : Finset V, D ⊆ U ∧ Hits J edge D ∧ 4 * D.card ≤ U.card + J.card := by
  classical
  obtain ⟨f⟩ := hcolor
  let X := twoVertices U J edge
  let fiber (c : Fin 4) : Finset ↥X := univ.filter fun v => f v = c
  obtain ⟨c, _, hmax⟩ := Finset.exists_max_image univ (fun c : Fin 4 => (fiber c).card)
    (by simp)
  let C := fiber c
  have hsum : (∑ d : Fin 4, (fiber d).card) = X.card := by
    simpa [fiber] using
      (Finset.sum_card_fiberwise_eq_card_filter (univ : Finset ↥X)
        (univ : Finset (Fin 4)) (fun v => f v))
  have hlarge : X.card ≤ 4 * C.card := by
    calc
      X.card = ∑ d : Fin 4, (fiber d).card := hsum.symm
      _ ≤ ∑ _d : Fin 4, C.card :=
        Finset.sum_le_sum fun d hd => hmax d hd
      _ = 4 * C.card := by simp
  let covered := C.biUnion fun v => incident J edge v.val
  have hcovered_sub : covered ⊆ J := by
    intro i hi
    obtain ⟨v, _, hv⟩ := mem_biUnion.mp hi
    exact (mem_incident.mp hv).1
  have hdis : (C : Set ↥X).PairwiseDisjoint (fun v => incident J edge v.val) := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro i hix hiy
    have hix' := mem_incident.mp hix
    have hiy' := mem_incident.mp hiy
    have hadj : (pairGraph U J edge).Adj x y :=
      ⟨hxy, i, hix'.1, hix'.2, hiy'.2⟩
    apply f.valid hadj
    have hx' : f x = c := (mem_filter.mp hx).2
    have hy' : f y = c := (mem_filter.mp hy).2
    exact hx'.trans hy'.symm
  have hcovered_card : covered.card = 2 * C.card := by
    rw [Finset.card_biUnion hdis]
    have ht : ∀ v ∈ C, (incident J edge v.val).card = 2 := by
      intro v _
      exact (mem_filter.mp v.property).2
    rw [Finset.sum_const_nat ht]
    omega
  let R := J \ covered
  have hex : ∀ i : ↥R, (edge i.val).Nonempty := by
    intro i
    apply card_pos.mp
    rw [hthree i.val (mem_sdiff.mp i.property).1]
    omega
  choose pick hpick using hex
  let D := C.image Subtype.val ∪ R.attach.image pick
  have hDsub : D ⊆ U := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨x, _, rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp x.property).1
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      exact hsub i.val (mem_sdiff.mp i.property).1 (hpick i)
  have hhits : Hits J edge D := by
    intro i hi
    by_cases hic : i ∈ covered
    · obtain ⟨v, hv, hvi⟩ := mem_biUnion.mp hic
      refine ⟨v.val, mem_union_left _ (mem_image.mpr ⟨v, hv, rfl⟩), ?_⟩
      exact (mem_incident.mp hvi).2
    · have hiR : i ∈ R := mem_sdiff.mpr ⟨hi, hic⟩
      refine ⟨pick ⟨i, hiR⟩, mem_union_right _ ?_, hpick ⟨i, hiR⟩⟩
      exact mem_image.mpr ⟨⟨i, hiR⟩, mem_attach _ _, rfl⟩
  have hDcard : D.card + C.card ≤ J.card := by
    have h1 := card_union_le (C.image Subtype.val) (R.attach.image pick)
    have h2 := card_image_le (s := R.attach) (f := pick)
    rw [card_attach] at h2
    rw [card_image_of_injective _ Subtype.val_injective] at h1
    change D.card ≤ C.card + (R.attach.image pick).card at h1
    have h3 := card_sdiff_add_card_eq_card hcovered_sub
    change R.card + covered.card = J.card at h3
    omega
  have hincidence := sum_incident_card U J edge hsub
  have hdegree_bound : (∑ v ∈ U, (incident J edge v).card) ≤ U.card + X.card := by
    calc
      (∑ v ∈ U, (incident J edge v).card) ≤
          ∑ v ∈ U, (1 + if (incident J edge v).card = 2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro v hv
        have hb := hdeg v hv
        split_ifs <;> omega
      _ = U.card + X.card := by
        rw [Finset.sum_add_distrib]
        have hones : (∑ _v ∈ U, (1 : ℕ)) = U.card := by simp
        rw [hones]
        congr 1
        rw [← Finset.sum_filter]
        change (∑ _v ∈ X, (1 : ℕ)) = X.card
        simp
  have hthree_sum : (∑ i ∈ J, (edge i).card) = 3 * J.card := by
    rw [Finset.sum_const_nat hthree]
    omega
  rw [hincidence, hthree_sum] at hdegree_bound
  exact ⟨D, hDsub, hhits, by omega⟩

end TotalDominationAnnihilationProof.Hypergraph

#print axioms TotalDominationAnnihilationProof.Hypergraph.pairGraph_degree_le_four
#print axioms TotalDominationAnnihilationProof.Hypergraph.pairGraph_cliqueFree_five
#print axioms TotalDominationAnnihilationProof.Hypergraph.three_cover_of_four_coloring
