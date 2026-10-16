import FormalConjectures.Gebendorfer.RegularMissCodes

/-! Explicit regular miss-codes attaining four and six members at every order
at least four, following Proposition 2.2 of the cited manuscript. -/

namespace RegularMissCodesProof
open Finset Gebendorfer.RegularMissCodes
set_option maxRecDepth 2000

def point (m : ℕ) (hm : 5 ≤ m) (i : Fin 4) : Fin m := ⟨i.val, by omega⟩

def sourceSet (m : ℕ) (hm : 5 ≤ m) (i : Fin 6) : Finset (Fin m) :=
  match i.val with
  | 0 => {point m hm 0}
  | 1 => {point m hm 1, point m hm 2}
  | 2 => {point m hm 0, point m hm 1, point m hm 2}
  | 3 => univ \ {point m hm 0, point m hm 1}
  | 4 => univ \ {point m hm 0, point m hm 2}
  | _ => univ \ {point m hm 1, point m hm 2}

def indices (third : Bool) : Finset (Fin 6) :=
  if third then univ else {0, 2, 3, 4}

def family (m : ℕ) (hm : 5 ≤ m) (third : Bool) : Finset (Finset (Fin m)) :=
  (indices third).image (sourceSet m hm)

theorem sourceSet_injective (m : ℕ) (hm : 5 ≤ m) :
    Function.Injective (sourceSet m hm) := by
  intro i j h
  have h0 := congrArg (fun S => point m hm 0 ∈ S) h
  have h1 := congrArg (fun S => point m hm 1 ∈ S) h
  have h2 := congrArg (fun S => point m hm 2 ∈ S) h
  have h3 := congrArg (fun S => point m hm 3 ∈ S) h
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceSet, point, Fin.ext_iff] at *

theorem sourceSet_card (m : ℕ) (hm : 5 ≤ m) (i : Fin 6) :
    (sourceSet m hm i).card =
      if i.val = 0 then 1 else if i.val = 1 then 2 else if i.val = 2 then 3 else m - 2 := by
  fin_cases i <;>
    norm_num [sourceSet, point, Fin.ext_iff, Finset.card_sdiff]

theorem sourceSet_size (m : ℕ) (hm : 5 ≤ m) (i : Fin 6) :
    (sourceSet m hm i).Nonempty ∧ (sourceSet m hm i).card ≤ m - 2 := by
  constructor
  · apply Finset.card_pos.mp
    rw [sourceSet_card]
    split_ifs <;> omega
  · rw [sourceSet_card]
    split_ifs <;> omega

theorem family_card (m : ℕ) (hm : 5 ≤ m) (third : Bool) :
    (family m hm third).card = if third then 6 else 4 := by
  rw [family, Finset.card_image_of_injective _ (sourceSet_injective m hm)]
  cases third <;> decide

theorem family_degree (m : ℕ) (hm : 5 ≤ m) (third : Bool) (v : Fin m) :
    ((family m hm third).filter fun S => v ∈ S).card = if third then 3 else 2 := by
  rw [family, Finset.filter_image,
    Finset.card_image_of_injective _ (sourceSet_injective m hm)]
  have hu : (univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by decide
  by_cases h0 : v = point m hm 0
  · subst v
    cases third <;> norm_num [indices, sourceSet, point, Fin.ext_iff, hu, Finset.filter_insert]
  by_cases h1 : v = point m hm 1
  · subst v
    cases third <;> norm_num [indices, sourceSet, point, Fin.ext_iff, hu, Finset.filter_insert]
  by_cases h2 : v = point m hm 2
  · subst v
    cases third <;> norm_num [indices, sourceSet, point, Fin.ext_iff, hu, Finset.filter_insert]
  cases third <;>
    simp [indices, sourceSet, hu, Finset.filter_insert, h0, h1, h2]

set_option maxHeartbeats 0 in
theorem family_closed (m : ℕ) (hm : 5 ≤ m) (third : Bool)
    (S T : Finset (Fin m)) (hS : S ∈ family m hm third)
    (hT : T ∈ family m hm third) (hc : (S ∪ T).card ≤ m - 2) :
    S ∪ T ∈ family m hm third := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hT
  let U := sourceSet m hm i ∪ sourceSet m hm j
  change U ∈ family m hm third
  change U.card ≤ m - 2 at hc
  cases third <;> fin_cases i <;> fin_cases j <;> norm_num [indices] at *
  all_goals
    first
    | (apply Finset.mem_image.mpr
       refine ⟨0, by norm_num [indices], ?_⟩
       ext v
       simp [U, sourceSet, point, Fin.ext_iff] <;> omega)
    | (apply Finset.mem_image.mpr
       refine ⟨1, by norm_num [indices], ?_⟩
       ext v
       simp [U, sourceSet, point, Fin.ext_iff] <;> omega)
    | (apply Finset.mem_image.mpr
       refine ⟨2, by norm_num [indices], ?_⟩
       ext v
       simp [U, sourceSet, point, Fin.ext_iff] <;> omega)
    | (apply Finset.mem_image.mpr
       refine ⟨3, by norm_num [indices], ?_⟩
       ext v
       simp [U, sourceSet, point, Fin.ext_iff] <;> omega)
    | (apply Finset.mem_image.mpr
       refine ⟨4, by norm_num [indices], ?_⟩
       ext v
       simp [U, sourceSet, point, Fin.ext_iff] <;> omega)
    | (apply Finset.mem_image.mpr
       refine ⟨5, by norm_num [indices], ?_⟩
       ext v
       simp [U, sourceSet, point, Fin.ext_iff] <;> omega)
    | (have hu : U = (univ \ {point m hm 0} : Finset (Fin m)) := by
         ext v
         simp [U, sourceSet, point, Fin.ext_iff] <;> omega
       rw [hu] at hc
       norm_num [Finset.card_sdiff] at hc
       omega)
    | (have hu : U = (univ \ {point m hm 1} : Finset (Fin m)) := by
         ext v
         simp [U, sourceSet, point, Fin.ext_iff] <;> omega
       rw [hu] at hc
       norm_num [Finset.card_sdiff] at hc
       omega)
    | (have hu : U = (univ \ {point m hm 2} : Finset (Fin m)) := by
         ext v
         simp [U, sourceSet, point, Fin.ext_iff] <;> omega
       rw [hu] at hc
       norm_num [Finset.card_sdiff] at hc
       omega)
    | (have hu : U = (univ : Finset (Fin m)) := by
         ext v
         simp [U, sourceSet, point, Fin.ext_iff] <;> omega
       rw [hu] at hc
       norm_num [Finset.card_sdiff] at hc
       omega)

theorem family_isMissCode (m : ℕ) (hm : 5 ≤ m) (third : Bool) :
    IsMissCode m (if third then 3 else 2) (family m hm third) := by
  refine ⟨?_, family_degree m hm third, ?_⟩
  · intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    exact sourceSet_size m hm i
  · intro S hS T hT hc
    exact family_closed m hm third S T hS hT hc

theorem degree_two_attained (m : ℕ) (hm : 4 ≤ m) :
    ∃ F : Finset (Finset (Fin m)), IsMissCode m 2 F ∧ F.card = 4 := by
  by_cases h4 : m = 4
  · subst m
    exact ⟨{{0, 1}, {1, 2}, {2, 3}, {3, 0}}, by unfold IsMissCode; decide, by decide⟩
  have h5 : 5 ≤ m := by omega
  exact ⟨family m h5 false, family_isMissCode m h5 false, family_card m h5 false⟩

theorem degree_three_attained (m : ℕ) (hm : 4 ≤ m) :
    ∃ F : Finset (Finset (Fin m)), IsMissCode m 3 F ∧ F.card = 6 := by
  by_cases h4 : m = 4
  · subst m
    exact ⟨{{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}}, by unfold IsMissCode; decide, by decide⟩
  have h5 : 5 ≤ m := by omega
  exact ⟨family m h5 true, family_isMissCode m h5 true, family_card m h5 true⟩

end RegularMissCodesProof

#print axioms RegularMissCodesProof.degree_two_attained
#print axioms RegularMissCodesProof.degree_three_attained
