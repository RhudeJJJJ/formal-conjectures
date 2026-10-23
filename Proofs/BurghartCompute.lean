import Proofs.BurghartIdeals
import Proofs.BurghartRep
/-! # Complete finite Burghart coefficient certificate
Duplikat-free generation is proved complete before kernel comparison. -/
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
namespace BurghartCertificate
open Finset

def fastList (a : Fin 28 → Finset (Fin 28)) : List (Fin 28) → List (Finset (Fin 28))
  | [] => [∅]
  | v :: vs => fastList a vs ++ ((fastList a vs).filter (fun S => decide (a v ⊆ insert v S))).map (insert v)

theorem fastList_subset (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28))
    (S : Finset (Fin 28)) (h : S ∈ fastList a vs) : S ⊆ vs.toFinset := by
  induction vs generalizing S with
  | nil => simpa [fastList] using h
  | cons v vs ih =>
    simp only [fastList,List.mem_append,List.mem_map,List.mem_filter,decide_eq_true_eq] at h
    rcases h with h | ⟨R,⟨hR,_⟩,rfl⟩
    · exact (ih S h).trans (by simp)
    · simpa only [List.toFinset_cons] using insert_subset_insert v (ih R hR)

theorem fastList_nodup (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28))
    (hn : vs.Nodup) : (fastList a vs).Nodup := by
  induction vs with
  | nil => simp [fastList]
  | cons v vs ih =>
    have hv := (List.nodup_cons.mp hn).1
    have ih := ih (List.nodup_cons.mp hn).2
    have hnot : ∀ S ∈ fastList a vs, v ∉ S := by
      intro S hS hmem
      exact hv (List.mem_toFinset.mp (fastList_subset a vs S hS hmem))
    rw [fastList,List.nodup_append]
    refine ⟨ih,?_,?_⟩
    · apply List.Nodup.map_on _ (ih.filter _)
      intro R hR S hS he
      have hR' := (List.mem_filter.mp hR).1
      have hS' := (List.mem_filter.mp hS).1
      simpa only [Finset.erase_insert (hnot R hR'),Finset.erase_insert (hnot S hS')] using
        congrArg (fun S => S.erase v) he
    · intro S hS T hT he
      obtain ⟨R,_,rfl⟩ := List.mem_map.mp hT
      exact hnot S hS (he.symm ▸ mem_insert_self v R)

theorem mem_fastList (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28))
    (S : Finset (Fin 28)) : S ∈ fastList a vs ↔ S ∈ generated a vs := by
  induction vs generalizing S with
  | nil => simp [fastList,generated]
  | cons v vs ih =>
    simp only [fastList,generated,extend,List.mem_append,List.mem_map,List.mem_filter,
      decide_eq_true_eq,Finset.mem_union,Finset.mem_image,Finset.mem_filter,ih]

def fastFinset (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28)) (hn : vs.Nodup) :
    Finset (Finset (Fin 28)) := ⟨fastList a vs, by simpa using fastList_nodup a vs hn⟩

theorem generated_eq_fast (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28)) (hn : vs.Nodup) :
    generated a vs = fastFinset a vs hn := by
  ext S
  change S ∈ generated a vs ↔ S ∈ fastList a vs
  exact (mem_fastList a vs S).symm

def admissiblesFast1 := fastFinset ancestors1 vertices1 (by decide +kernel)
def admissiblesFast2 := fastFinset ancestors2 vertices2 (by decide +kernel)

open scoped Classical in
theorem admissiblesFast1_eq : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible T1 0) = admissiblesFast1 := by
  rw [admissibles1_eq]
  exact generated_eq_fast _ _ _
open scoped Classical in
theorem admissiblesFast2_eq : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible T2 0) = admissiblesFast2 := by
  rw [admissibles2_eq]
  exact generated_eq_fast _ _ _

theorem admissiblesFast1_card : admissiblesFast1.card = 325 := by decide +kernel
#print axioms admissiblesFast1_card
theorem admissiblesFast2_card : admissiblesFast2.card = 325 := by decide +kernel
#print axioms admissiblesFast2_card
set_option maxHeartbeats 0 in
theorem equal_reps_fast : repOf T1 distances1 admissiblesFast1 = repOf T2 distances2 admissiblesFast2 := by
  decide +kernel
#print axioms equal_reps_fast
end BurghartCertificate
