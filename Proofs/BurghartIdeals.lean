import Proofs.BurghartBase

/-! # BurghartIdeals
Exact-definition certificate for Burghart Conjecture 20.
All finite computations are checked by the Lean kernel. -/

namespace BurghartCertificate
open Finset

def Ideal (a : Fin 28 → Finset (Fin 28)) (S : Finset (Fin 28)) : Prop :=
  ∀ v ∈ S, a v ⊆ S
instance (a : Fin 28 → Finset (Fin 28)) (S : Finset (Fin 28)) : Decidable (Ideal a S) :=
  inferInstanceAs (Decidable (∀ v ∈ S, a v ⊆ S))

def extend (a : Fin 28 → Finset (Fin 28)) (v : Fin 28)
    (C : Finset (Finset (Fin 28))) : Finset (Finset (Fin 28)) :=
  C ∪ (C.filter (fun S => a v ⊆ insert v S)).image (insert v)

theorem extend_eq (a : Fin 28 → Finset (Fin 28)) (U : Finset (Fin 28)) (v : Fin 28)
    (ha : ∀ u ∈ U, v ∉ a u) :
    (insert v U).powerset.filter (Ideal a) = extend a v (U.powerset.filter (Ideal a)) := by
  classical
  ext S
  simp only [mem_filter,mem_powerset,extend,mem_union,mem_image]
  constructor
  · rintro ⟨hS,hI⟩
    by_cases hv : v ∈ S
    · right
      refine ⟨S.erase v,⟨⟨?_,?_⟩,?_⟩,insert_erase hv⟩
      · intro u hu
        have hs := hS (mem_of_mem_erase hu)
        exact (mem_insert.mp hs).resolve_left (ne_of_mem_erase hu)
      · intro u hu w hw
        refine mem_erase.mpr ⟨?_,hI u (mem_of_mem_erase hu) hw⟩
        intro he
        subst w
        exact ha u ((mem_insert.mp (hS (mem_of_mem_erase hu))).resolve_left (ne_of_mem_erase hu)) hw
      · simpa only [insert_erase hv] using hI v hv
    · left
      exact ⟨fun u hu => (mem_insert.mp (hS hu)).resolve_left (fun he => hv (he ▸ hu)),hI⟩
  · rintro (⟨hS,hI⟩ | ⟨R,⟨⟨hR,hI⟩,hv⟩,rfl⟩)
    · exact ⟨hS.trans (subset_insert _ _),hI⟩
    · refine ⟨insert_subset_insert v hR,?_⟩
      intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · exact hv
      · exact (hI u hu).trans (subset_insert _ _)

def generated (a : Fin 28 → Finset (Fin 28)) : List (Fin 28) → Finset (Finset (Fin 28))
  | [] => {∅}
  | v :: vs => extend a v (generated a vs)

def Ordered (a : Fin 28 → Finset (Fin 28)) : List (Fin 28) → Prop
  | [] => True
  | v :: vs => (∀ u ∈ vs, v ∉ a u) ∧ Ordered a vs
instance (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28)) : Decidable (Ordered a vs) := by
  induction vs with
  | nil => exact isTrue trivial
  | cons v vs ih => exact inferInstanceAs (Decidable ((∀ u ∈ vs, v ∉ a u) ∧ Ordered a vs))

theorem generated_eq (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28))
    (h : Ordered a vs) : vs.toFinset.powerset.filter (Ideal a) = generated a vs := by
  induction vs with
  | nil => simp [generated,Ideal]
  | cons v vs ih =>
    rw [List.toFinset_cons,extend_eq a _ v (by simpa using h.1),ih h.2]
    rfl

theorem closed_iff_ideal (G : SimpleGraph (Fin 28)) (r : Fin 28 → Fin 28 → List (Fin 28))
    (hr : RoutesOK G r) (S : Finset (Fin 28)) :
    ClosedCode r S ↔ Ideal (fun v => (r 0 v).toFinset) S := by
  constructor
  · rintro (rfl | ⟨_,h⟩)
    · intro v hv; simp at hv
    · exact h
  · intro h
    by_cases he : S = ∅
    · exact Or.inl he
    · obtain ⟨v,hv⟩ := nonempty_iff_ne_empty.mpr he
      exact Or.inr ⟨h v hv (List.mem_toFinset.mpr (List.mem_of_head? (hr.first 0 v))),h⟩

def ancestors1 (v : Fin 28) : Finset (Fin 28) := (([[0],[0,1],[0,1,2],[0,1,2,3],[0,1,2,3,4],[0,1,2,3,4,5],[0,1,2,3,4,5,6],[0,1,2,3,4,5,7],[0,1,2,3,8],[0,1,2,9],[0,1,2,9,10],[0,1,2,11],[0,1,2,11,12],[0,1,2,13],[0,14],[0,14,15],[0,14,15,16],[0,14,15,16,17],[0,14,15,16,17,18],[0,14,15,16,17,18,19],[0,14,15,16,17,20],[0,14,15,21],[0,14,15,21,22],[0,14,15,21,23],[0,14,15,24],[0,14,15,24,25],[0,14,15,24,26],[0,14,27]]: List (List (Fin 28))).getD v.val []).toFinset
def ancestors2 (v : Fin 28) : Finset (Fin 28) := (([[0],[0,1],[0,1,2],[0,1,2,3],[0,1,2,3,4],[0,1,2,3,4,5],[0,1,2,3,4,5,6],[0,1,2,3,4,5,7],[0,1,2,3,8],[0,1,2,9],[0,1,2,9,10],[0,1,2,9,11],[0,1,2,12],[0,1,2,12,13],[0,1,14],[0,15],[0,15,16],[0,15,16,17],[0,15,16,17,18],[0,15,16,17,18,19],[0,15,16,17,18,19,20],[0,15,16,17,18,21],[0,15,16,22],[0,15,16,22,23],[0,15,16,22,24],[0,15,16,25],[0,15,16,25,26],[0,15,16,27]]: List (List (Fin 28))).getD v.val []).toFinset

def vertices1 : List (Fin 28) := [24,21,18,17,16,15,14,11,9,5,4,3,2,1,0]
def vertices2 : List (Fin 28) := [25,22,19,18,17,16,15,12,9,5,4,3,2,1,0]
def distances1 (u v : Fin 28) : ℕ := (([[0,1,2,3,4,5,6,6,4,3,4,3,4,3,1,2,3,4,5,6,5,3,4,4,3,4,4,2],[1,0,1,2,3,4,5,5,3,2,3,2,3,2,2,3,4,5,6,7,6,4,5,5,4,5,5,3],[2,1,0,1,2,3,4,4,2,1,2,1,2,1,3,4,5,6,7,8,7,5,6,6,5,6,6,4],[3,2,1,0,1,2,3,3,1,2,3,2,3,2,4,5,6,7,8,9,8,6,7,7,6,7,7,5],[4,3,2,1,0,1,2,2,2,3,4,3,4,3,5,6,7,8,9,10,9,7,8,8,7,8,8,6],[5,4,3,2,1,0,1,1,3,4,5,4,5,4,6,7,8,9,10,11,10,8,9,9,8,9,9,7],[6,5,4,3,2,1,0,2,4,5,6,5,6,5,7,8,9,10,11,12,11,9,10,10,9,10,10,8],[6,5,4,3,2,1,2,0,4,5,6,5,6,5,7,8,9,10,11,12,11,9,10,10,9,10,10,8],[4,3,2,1,2,3,4,4,0,3,4,3,4,3,5,6,7,8,9,10,9,7,8,8,7,8,8,6],[3,2,1,2,3,4,5,5,3,0,1,2,3,2,4,5,6,7,8,9,8,6,7,7,6,7,7,5],[4,3,2,3,4,5,6,6,4,1,0,3,4,3,5,6,7,8,9,10,9,7,8,8,7,8,8,6],[3,2,1,2,3,4,5,5,3,2,3,0,1,2,4,5,6,7,8,9,8,6,7,7,6,7,7,5],[4,3,2,3,4,5,6,6,4,3,4,1,0,3,5,6,7,8,9,10,9,7,8,8,7,8,8,6],[3,2,1,2,3,4,5,5,3,2,3,2,3,0,4,5,6,7,8,9,8,6,7,7,6,7,7,5],[1,2,3,4,5,6,7,7,5,4,5,4,5,4,0,1,2,3,4,5,4,2,3,3,2,3,3,1],[2,3,4,5,6,7,8,8,6,5,6,5,6,5,1,0,1,2,3,4,3,1,2,2,1,2,2,2],[3,4,5,6,7,8,9,9,7,6,7,6,7,6,2,1,0,1,2,3,2,2,3,3,2,3,3,3],[4,5,6,7,8,9,10,10,8,7,8,7,8,7,3,2,1,0,1,2,1,3,4,4,3,4,4,4],[5,6,7,8,9,10,11,11,9,8,9,8,9,8,4,3,2,1,0,1,2,4,5,5,4,5,5,5],[6,7,8,9,10,11,12,12,10,9,10,9,10,9,5,4,3,2,1,0,3,5,6,6,5,6,6,6],[5,6,7,8,9,10,11,11,9,8,9,8,9,8,4,3,2,1,2,3,0,4,5,5,4,5,5,5],[3,4,5,6,7,8,9,9,7,6,7,6,7,6,2,1,2,3,4,5,4,0,1,1,2,3,3,3],[4,5,6,7,8,9,10,10,8,7,8,7,8,7,3,2,3,4,5,6,5,1,0,2,3,4,4,4],[4,5,6,7,8,9,10,10,8,7,8,7,8,7,3,2,3,4,5,6,5,1,2,0,3,4,4,4],[3,4,5,6,7,8,9,9,7,6,7,6,7,6,2,1,2,3,4,5,4,2,3,3,0,1,1,3],[4,5,6,7,8,9,10,10,8,7,8,7,8,7,3,2,3,4,5,6,5,3,4,4,1,0,2,4],[4,5,6,7,8,9,10,10,8,7,8,7,8,7,3,2,3,4,5,6,5,3,4,4,1,2,0,4],[2,3,4,5,6,7,8,8,6,5,6,5,6,5,1,2,3,4,5,6,5,3,4,4,3,4,4,0]]: List (List ℕ)).getD u.val []).getD v.val 0
def distances2 (u v : Fin 28) : ℕ := (([[0,1,2,3,4,5,6,6,4,3,4,4,3,4,2,1,2,3,4,5,6,5,3,4,4,3,4,3],[1,0,1,2,3,4,5,5,3,2,3,3,2,3,1,2,3,4,5,6,7,6,4,5,5,4,5,4],[2,1,0,1,2,3,4,4,2,1,2,2,1,2,2,3,4,5,6,7,8,7,5,6,6,5,6,5],[3,2,1,0,1,2,3,3,1,2,3,3,2,3,3,4,5,6,7,8,9,8,6,7,7,6,7,6],[4,3,2,1,0,1,2,2,2,3,4,4,3,4,4,5,6,7,8,9,10,9,7,8,8,7,8,7],[5,4,3,2,1,0,1,1,3,4,5,5,4,5,5,6,7,8,9,10,11,10,8,9,9,8,9,8],[6,5,4,3,2,1,0,2,4,5,6,6,5,6,6,7,8,9,10,11,12,11,9,10,10,9,10,9],[6,5,4,3,2,1,2,0,4,5,6,6,5,6,6,7,8,9,10,11,12,11,9,10,10,9,10,9],[4,3,2,1,2,3,4,4,0,3,4,4,3,4,4,5,6,7,8,9,10,9,7,8,8,7,8,7],[3,2,1,2,3,4,5,5,3,0,1,1,2,3,3,4,5,6,7,8,9,8,6,7,7,6,7,6],[4,3,2,3,4,5,6,6,4,1,0,2,3,4,4,5,6,7,8,9,10,9,7,8,8,7,8,7],[4,3,2,3,4,5,6,6,4,1,2,0,3,4,4,5,6,7,8,9,10,9,7,8,8,7,8,7],[3,2,1,2,3,4,5,5,3,2,3,3,0,1,3,4,5,6,7,8,9,8,6,7,7,6,7,6],[4,3,2,3,4,5,6,6,4,3,4,4,1,0,4,5,6,7,8,9,10,9,7,8,8,7,8,7],[2,1,2,3,4,5,6,6,4,3,4,4,3,4,0,3,4,5,6,7,8,7,5,6,6,5,6,5],[1,2,3,4,5,6,7,7,5,4,5,5,4,5,3,0,1,2,3,4,5,4,2,3,3,2,3,2],[2,3,4,5,6,7,8,8,6,5,6,6,5,6,4,1,0,1,2,3,4,3,1,2,2,1,2,1],[3,4,5,6,7,8,9,9,7,6,7,7,6,7,5,2,1,0,1,2,3,2,2,3,3,2,3,2],[4,5,6,7,8,9,10,10,8,7,8,8,7,8,6,3,2,1,0,1,2,1,3,4,4,3,4,3],[5,6,7,8,9,10,11,11,9,8,9,9,8,9,7,4,3,2,1,0,1,2,4,5,5,4,5,4],[6,7,8,9,10,11,12,12,10,9,10,10,9,10,8,5,4,3,2,1,0,3,5,6,6,5,6,5],[5,6,7,8,9,10,11,11,9,8,9,9,8,9,7,4,3,2,1,2,3,0,4,5,5,4,5,4],[3,4,5,6,7,8,9,9,7,6,7,7,6,7,5,2,1,2,3,4,5,4,0,1,1,2,3,2],[4,5,6,7,8,9,10,10,8,7,8,8,7,8,6,3,2,3,4,5,6,5,1,0,2,3,4,3],[4,5,6,7,8,9,10,10,8,7,8,8,7,8,6,3,2,3,4,5,6,5,1,2,0,3,4,3],[3,4,5,6,7,8,9,9,7,6,7,7,6,7,5,2,1,2,3,4,5,4,2,3,3,0,1,2],[4,5,6,7,8,9,10,10,8,7,8,8,7,8,6,3,2,3,4,5,6,5,3,4,4,1,0,3],[3,4,5,6,7,8,9,9,7,6,7,7,6,7,5,2,1,2,3,4,5,4,2,3,3,2,3,0]]: List (List ℕ)).getD u.val []).getD v.val 0

theorem ancestors1_eq : (fun v => (route1 0 v).toFinset) = ancestors1 := by
  funext v
  have h : ∀ v : Fin 28, (route1 0 v).toFinset = ancestors1 v := by decide +kernel
  exact h v
theorem ancestors2_eq : (fun v => (route2 0 v).toFinset) = ancestors2 := by
  funext v
  have h : ∀ v : Fin 28, (route2 0 v).toFinset = ancestors2 v := by decide +kernel
  exact h v
theorem distances1_eq : distanceCode route1 = distances1 := by
  funext u v
  have h : ∀ u v : Fin 28, distanceCode route1 u v = distances1 u v := by decide +kernel
  exact h u v
theorem distances2_eq : distanceCode route2 = distances2 := by
  funext u v
  have h : ∀ u v : Fin 28, distanceCode route2 u v = distances2 u v := by decide +kernel
  exact h u v

theorem ordered1 : Ordered ancestors1 vertices1 := by decide +kernel
theorem ordered2 : Ordered ancestors2 vertices2 := by decide +kernel

def admissibles1 := generated ancestors1 vertices1
def admissibles2 := generated ancestors2 vertices2

theorem vertices1_eq : univ \ leavesCode T1 distances1 = vertices1.toFinset := by decide +kernel
theorem vertices2_eq : univ \ leavesCode T2 distances2 = vertices2.toFinset := by decide +kernel

open scoped Classical in
theorem admissibles1_eq : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible T1 0) = admissibles1 := by
  rw [admissibles_eq_code T1 route1 route1_ok T1_tree,distances1_eq]
  simp only [closed_iff_ideal T1 route1 route1_ok,ancestors1_eq]
  rw [vertices1_eq,generated_eq _ _ ordered1]
  rfl
open scoped Classical in
theorem admissibles2_eq : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible T2 0) = admissibles2 := by
  rw [admissibles_eq_code T2 route2 route2_ok T2_tree,distances2_eq]
  simp only [closed_iff_ideal T2 route2 route2_ok,ancestors2_eq]
  rw [vertices2_eq,generated_eq _ _ ordered2]
  rfl

#print axioms admissibles1_eq
#print axioms admissibles2_eq

end BurghartCertificate
