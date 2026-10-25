import Proofs.WOWII376354.TreeCounting

/-! Maximum-degree isolates and the exclusion of saturated tree-half covers. -/

open Finset SimpleGraph
namespace WOWIIMedian
open WrittenOnTheWallII.GraphConjecture376
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : SimpleGraph V) [DecidableRel T.Adj]

def delta : ℕ := univ.sup T.degree

omit [DecidableEq V] in
lemma degree_le_delta (v : V) : T.degree v ≤ delta T := Finset.le_sup (mem_univ v)

omit [DecidableEq V] in
lemma maximum_iff {v : V} : v ∈ maximumVertices T ↔ T.degree v=delta T := by
  classical
  simp only [maximumVertices,mem_filter,mem_univ,true_and]
  constructor
  · intro h
    exact le_antisymm (degree_le_delta T v) (Finset.sup_le (fun w _ => h w))
  · intro h w
    exact (degree_le_delta T w).trans_eq h.symm

lemma isolate_iff {v : V} : v ∈ maximumDegreeIsolates T ↔
    v ∈ maximumVertices T ∧ ∀ w ∈ maximumVertices T, ¬T.Adj v w := by
  classical
  simp only [maximumDegreeIsolates,mem_filter]

lemma isolates_independent : ∀ u ∈ maximumDegreeIsolates T,
    ∀ v ∈ maximumDegreeIsolates T, ¬T.Adj u v := by
  intro u hu v hv
  exact ((isolate_iff T).mp hu).2 v ((isolate_iff T).mp hv).1

lemma isolates_degree_sum (I : Finset V) (hI : I ⊆ maximumDegreeIsolates T) :
    ∑ u ∈ I, T.degree u=delta T*I.card := by
  have h : ∀ u ∈ I, T.degree u=delta T :=
    fun u hu => (maximum_iff T).mp ((isolate_iff T).mp (hI hu)).1
  simp only [Finset.sum_congr rfl h,Finset.sum_const,Nat.nsmul_eq_mul]
  exact Nat.mul_comm _ _

lemma delta_ge_two (hT : T.IsTree) (ho : 2<Fintype.card V) : 2≤delta T := by
  by_contra hn
  have hd : ∀ v, T.degree v≤1 := fun v => (degree_le_delta T v).trans (by omega)
  have hsum : ∑ v : V, T.degree v≤Fintype.card V := by
    calc
      _ ≤ ∑ _v : V, 1 := Finset.sum_le_sum (fun v _ => hd v)
      _ = _ := by simp
  have he := hT.card_edgeFinset
  have hs := T.sum_degrees_eq_twice_card_edges
  omega

lemma total_cover_delta {D : Finset V} (hD : T.IsTotalDominating (D : Set V)) :
    Fintype.card V ≤ ∑ d ∈ D, T.degree d ∧
      (∑ d ∈ D, T.degree d) ≤ delta T*D.card := by
  classical
  refine ⟨?_,?_⟩
  · simpa only [card_univ] using cover_sum_bound T univ D (fun v _ => hD v)
  · calc
      _ ≤ ∑ _d ∈ D, delta T := Finset.sum_le_sum (fun d _ => degree_le_delta T d)
      _ = _ := by simp [Nat.mul_comm]

lemma total_cover_strict {D : Finset V} (hD : T.IsTotalDominating (D : Set V))
    (hI : (maximumDegreeIsolates T).Nonempty) : Fintype.card V < delta T*D.card := by
  classical
  obtain ⟨i,hi⟩ := hI
  obtain ⟨d,hd,hid⟩ := hD i
  have hnot : d ∉ maximumVertices T := fun h => ((isolate_iff T).mp hi).2 d h hid
  have hdeg : T.degree d<delta T := by
    have hl := degree_le_delta T d
    have hne : T.degree d≠delta T := fun h => hnot ((maximum_iff T).mpr h)
    omega
  have hs : ∑ x ∈ D, T.degree x < ∑ _x ∈ D, delta T := by
    exact Finset.sum_lt_sum (fun x _ => degree_le_delta T x) ⟨d,hd,hdeg⟩
  have hh := (total_cover_delta T hD).1.trans_lt hs
  simpa only [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm] using hh

lemma basic_isolate_bound (hT : T.IsTree) {D : Finset V}
    (hD : T.IsTotalDominating (D : Set V)) : (maximumDegreeIsolates T).card+1 ≤ D.card := by
  have hi := independent_global_bound T hT (maximumDegreeIsolates T) (isolates_independent T)
  rw [isolates_degree_sum T _ (subset_refl _)] at hi
  have hd := (total_cover_delta T hD).1.trans (total_cover_delta T hD).2
  by_contra hn
  have hc : D.card ≤ (maximumDegreeIsolates T).card := by omega
  have hm := Nat.mul_le_mul_left (delta T) hc
  omega

lemma half_isolate_bound (hT : T.IsTree) {a b : V} (hab : T.Adj a b) :
    delta T*((maximumDegreeIsolates T) ∩ side T a b).card ≤
      (side T a b).card-1+(if a ∈ maximumDegreeIsolates T then 1 else 0) := by
  have h := independent_side_bound T hT hab
    ((maximumDegreeIsolates T) ∩ side T a b) inter_subset_right (by
      intro u hu v hv
      exact isolates_independent T u (mem_inter.mp hu).1 v (mem_inter.mp hv).1)
  rw [isolates_degree_sum T _ inter_subset_left] at h
  have ha := side_root T hab
  simpa only [mem_inter,ha,and_true] using h

lemma saturated_half (hT : T.IsTree) {a b : V} (hab : T.Adj a b)
    {D : Finset V} (hD : T.IsTotalDominating (D : Set V))
    (hh : 2≤(side T a b).card)
    (hsat : delta T*(D ∩ side T a b).card=(side T a b).card-1) :
    (maximumDegreeIsolates T ∩ side T a b).card < (D ∩ side T a b).card := by
  classical
  let S := side T a b
  let E := D ∩ S
  have hupper : ∀ d ∈ E, internalDegree T S d≤delta T := by
    intro d hd
    exact (internal_le_degree T S d).trans (degree_le_delta T d)
  have hbound := side_cover_bound T hT hab hD
  have hsumUpper : ∑ d ∈ E, internalDegree T S d ≤ delta T*E.card := by
    calc
      _ ≤ ∑ _d ∈ E, delta T := Finset.sum_le_sum hupper
      _ = _ := by simp [Nat.mul_comm]
  have hall : ∀ d ∈ E, internalDegree T S d=delta T := by
    intro d hd
    by_contra hn
    have hlt : internalDegree T S d<delta T := lt_of_le_of_ne (hupper d hd) hn
    have hstrict := Finset.sum_lt_sum hupper ⟨d,hd,hlt⟩
    have hsumConst : (∑ _d ∈ E, delta T)=delta T*E.card := by simp [Nat.mul_comm]
    rw [hsumConst] at hstrict
    change S.card-1≤∑ d ∈ E, internalDegree T S d at hbound
    change delta T*E.card=S.card-1 at hsat
    omega
  have hmax : ∀ d ∈ E, d ∈ maximumVertices T := by
    intro d hd
    apply (maximum_iff T).mpr
    have hl := internal_le_degree T S d
    have hr := degree_le_delta T d
    rw [hall d hd] at hl
    omega
  have hb : b ∉ S := by
    have hb' := side_root T hab.symm
    rw [side_compl T hT hab] at hb'
    exact mem_compl.mp hb'
  have haE : a ∉ E := by
    intro haE
    have hlt := internal_lt_at_boundary T hab hb
    have hmaxa := degree_le_delta T a
    rw [hall a haE] at hlt
    omega
  have inside : ∀ x ∈ S, x≠a → ∀ d, T.Adj x d → d ∈ S := by
    intro x hx hxa d hxd
    by_contra hd
    have hd' : d ∈ side T b a := by rw [side_compl T hT hab];simpa using hd
    exact hxa (side_cross_edge T hT hab hx hd' hxd).1
  have hI : maximumDegreeIsolates T ∩ S ⊆ {a} := by
    intro i hi
    apply mem_singleton.mpr
    by_contra hia
    obtain ⟨d,hd,hid⟩ := hD i
    have hdE : d ∈ E := mem_inter.mpr ⟨hd,inside i (mem_inter.mp hi).2 hia d hid⟩
    exact ((isolate_iff T).mp (mem_inter.mp hi).1).2 d (hmax d hdE) hid
  have hiCard : (maximumDegreeIsolates T ∩ S).card ≤ 1 :=
    (card_le_card hI).trans_eq (card_singleton a)
  have hEpos : 0<E.card := by
    change delta T*E.card=S.card-1 at hsat
    change 2≤S.card at hh
    by_contra hn
    have hz : E.card=0 := by omega
    rw [hz,Nat.mul_zero] at hsat
    omega
  have hElarge : 2≤E.card := by
    by_contra hn
    have he : E.card=1 := by omega
    obtain ⟨x,hx⟩ := card_eq_one.mp he
    have hxE : x ∈ E := by rw [hx];exact mem_singleton_self _
    have hxS := (mem_inter.mp hxE).2
    have hxa : x≠a := by intro h;subst x;exact haE hxE
    obtain ⟨d,hd,hxd⟩ := hD x
    have hdE : d ∈ E := mem_inter.mpr ⟨hd,inside x hxS hxa d hxd⟩
    rw [hx,mem_singleton] at hdE
    subst d
    exact hxd.ne rfl
  change (maximumDegreeIsolates T ∩ S).card < E.card
  omega

end WOWIIMedian
