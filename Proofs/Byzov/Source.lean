module

public import FormalConjectures.Arxiv.«2603.07707».AutomorphismGroup
public import Proofs.Byzov.Model

/-! # Exact bridge from Equation (17) to the canonical profile model

All adjacency statements here use the original imported ByzovPushkarev.adjacent.
The two-sided profiles and the twin exchanges are proved from those exponent sets.
-/

@[expose] public section
namespace ByzovPushkarev.Certificate
open Finset

theorem modulus_zero (n : ℕ) : (2 : C n)*(n : C n)+3 = 0 := by
  have h : ((2*n+3 : ℕ) : C n) = 0 := ZMod.natCast_self (M n)
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using h

theorem mem_shift {n : ℕ} (a : C n) (E : Finset (C n)) (r : C n) :
    r ∈ shiftSet a E ↔ r-a ∈ E := by
  constructor
  · intro h
    obtain ⟨t,ht,he⟩ := mem_image.1 h
    rw [← he,add_sub_cancel_right]
    exact ht
  · intro h
    exact mem_image.2 ⟨r-a,h,sub_add_cancel r a⟩

@[simp] theorem shift_zero {n : ℕ} (E : Finset (C n)) : shiftSet 0 E = E := by
  simp [shiftSet]

theorem pSet_interval (n : ℕ) : pSet n = interval (n+1) (0 : C n) := by
  simp only [pSet,interval,zero_add]

instance adjacentDecidable (n : ℕ) : DecidableRel (adjacent n) := by
  intro u v
  unfold adjacent
  infer_instance

def outProfile (n : ℕ) (u : V n) : Finset (C n) :=
  univ.filter fun t => adjacent n u (3,t)

def inProfile (n : ℕ) (u : V n) : Finset (C n) :=
  univ.filter fun t => adjacent n (3,t) u

@[simp] theorem mem_outProfile (n : ℕ) (u : V n) (t : C n) :
    t ∈ outProfile n u ↔ adjacent n u (3,t) := by simp [outProfile]

@[simp] theorem mem_inProfile (n : ℕ) (u : V n) (t : C n) :
    t ∈ inProfile n u ↔ adjacent n (3,t) u := by simp [inProfile]

theorem outProfile_eq (n : ℕ) (u : V n) : outProfile n u = outShape n u := by
  ext t
  rw [mem_outProfile]
  unfold adjacent
  by_cases hi : u.1.val < 6
  · rw [if_pos hi]
    change t-u.2 ∈ shiftSet (u.1.val : C n) (shiftSet ((n-1 : ℕ) : C n) (pSet n)) ↔ _
    rw [mem_shift,mem_shift,pSet_interval,mem_interval (by dsimp [M]; omega)]
    simp only [outShape,if_pos hi]
    rw [mem_interval (by dsimp [M]; omega)]
    simp only [sub_zero]
    have he : t-u.2-(u.1.val : C n)-((n-1 : ℕ) : C n) =
        t-(u.2+(u.1.val : C n)+((n-1 : ℕ) : C n)) := by ring
    rw [he]
  · rw [if_neg hi]
    change t-u.2 ∈ {((n-1 : ℕ) : C n)} ↔ _
    simp only [outShape,if_neg hi,mem_singleton]
    constructor <;> intro h <;> linear_combination h

theorem incoming_interval (n : ℕ) (a z : C n) :
    (univ.filter fun t : C n => z-t ∈ shiftSet 3 (shiftSet a (pSet n))) =
      interval (n+1) (z-3-a-(n : C n)) := by
  ext t
  simp only [mem_filter,mem_univ,true_and,mem_shift,pSet_interval]
  rw [mem_interval (by dsimp [M]; omega),mem_interval (by dsimp [M]; omega)]
  simp only [sub_zero]
  have he : t-(z-3-a-(n : C n)) = (n : C n)-((z-t)-3-a) := by ring
  rw [he]
  simpa only [Nat.add_sub_cancel] using
    (val_reflection (q := n+1) (by omega) (by dsimp [M]; omega) (((z-t)-3)-a))

theorem incoming_p (n : ℕ) (z : C n) :
    (univ.filter fun t : C n => z-t ∈ shiftSet 3 (pSet n)) =
      interval (n+1) (z-3-(n : C n)) := by
  simpa only [shift_zero,sub_zero] using incoming_interval n 0 z

theorem incoming_singleton (n : ℕ) (a z : C n) :
    (univ.filter fun t : C n => z-t ∈ shiftSet 3 {a}) = {z-3-a} := by
  ext t
  simp only [mem_filter,mem_univ,true_and,mem_shift,mem_singleton]
  constructor <;> intro h <;> linear_combination -h

theorem incoming_pair (n : ℕ) (a b z : C n) :
    (univ.filter fun t : C n => z-t ∈ shiftSet 3 {a,b}) = {z-3-a,z-3-b} := by
  ext t
  simp only [mem_filter,mem_univ,true_and,mem_shift,mem_insert,mem_singleton]
  constructor
  · rintro (h|h)
    · left; linear_combination -h
    · right; linear_combination -h
  · rintro (h|h)
    · left; linear_combination -h
    · right; linear_combination -h

theorem inProfile_eq (n : ℕ) (hn : 2 ≤ n) (u : V n) :
    inProfile n u = inShape n u := by
  obtain ⟨i,z⟩ := u
  have hi : inProfile n (i,z) =
      (univ.filter fun t : C n => z-t ∈ shiftSet 3 (rowA n i)) := rfl
  rw [hi]
  have hM := modulus_zero n
  have hc1 : ((n-1 : ℕ) : C n) = (n : C n)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hc2 : ((n-2 : ℕ) : C n) = (n : C n)-2 := by
    rw [Nat.cast_sub hn,Nat.cast_ofNat]
  have hc21 : ((2*n-1 : ℕ) : C n) = 2*(n : C n)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*n),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  fin_cases i
  · simp [rowA,inShape,shiftSet]
  · change (univ.filter fun t : C n => z-t ∈ shiftSet 3 (pSet n)) = interval (n+1) (z+(n : C n))
    rw [incoming_p]
    congr 1
    linear_combination -hM
  · change (univ.filter fun t : C n => z-t ∈ shiftSet 3 (shiftSet 1 (pSet n))) =
      interval (n+1) (z+((n-1 : ℕ) : C n))
    rw [incoming_interval]
    congr 1
    rw [hc1]
    linear_combination -hM
  · change (univ.filter fun t : C n => z-t ∈ shiftSet 3 (shiftSet ((n-1 : ℕ) : C n) (pSet n))) =
      interval (n+1) (z+1)
    rw [incoming_interval]
    congr 1
    rw [hc1]
    linear_combination -hM
  · change (univ.filter fun t : C n => z-t ∈ shiftSet 3 (shiftSet ((n-2 : ℕ) : C n) (pSet n))) =
      interval (n+1) (z+2)
    rw [incoming_interval]
    congr 1
    rw [hc2]
    linear_combination -hM
  · change (univ.filter fun t : C n => z-t ∈ shiftSet 3 {((2*n : ℕ) : C n)}) = {z}
    rw [incoming_singleton]
    congr 1
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    linear_combination -hM
  · change (univ.filter fun t : C n => z-t ∈ shiftSet 3 {1,((n+1 : ℕ) : C n)}) =
      {z+((n-1 : ℕ) : C n),z+((2*n-1 : ℕ) : C n)}
    rw [incoming_pair]
    have ha : z-3-1 = z+((2*n-1 : ℕ) : C n) := by
      rw [hc21]
      linear_combination -hM
    have hb : z-3-((n+1 : ℕ) : C n) = z+((n-1 : ℕ) : C n) := by
      rw [Nat.cast_add,Nat.cast_one,hc1]
      linear_combination -hM
    rw [ha,hb,pair_comm]
  · change (univ.filter fun t : C n => z-t ∈ shiftSet 3 (shiftSet 2 (pSet n))) =
      interval (n+1) (z+((n-2 : ℕ) : C n))
    rw [incoming_interval]
    congr 1
    rw [hc2]
    linear_combination -hM
  · change (univ.filter fun t : C n => z-t ∈ shiftSet 3 (shiftSet 1 (pSet n))) =
      interval (n+1) (z+((n-1 : ℕ) : C n))
    rw [incoming_interval]
    congr 1
    rw [hc1]
    linear_combination -hM

theorem adjacent_translate (n : ℕ) (c : C n) (u v : V n) :
    adjacent n (translate c u) (translate c v) ↔ adjacent n u v := by
  dsimp [adjacent,translate]
  have he : (v.2+c)-(u.2+c) = v.2-u.2 := by ring
  rw [he]

theorem adjacent_canon_left (n : ℕ) (u v : V n) :
    adjacent n u v ↔ adjacent n (canon u) v := by
  obtain ⟨i,z⟩ := u
  by_cases hi : i = 4
  · subst i
    change v.2-z ∈ shiftSet 4 (rowA n v.1) ↔
      v.2-(z+1) ∈ shiftSet 3 (rowA n v.1)
    rw [mem_shift,mem_shift]
    have he : v.2-z-4 = v.2-(z+1)-3 := by ring
    rw [he]
  · simp only [canon,if_neg hi]

theorem adjacent_canon_right (n : ℕ) (hn : 2 ≤ n) (u v : V n) :
    adjacent n u v ↔ adjacent n u (canon v) := by
  obtain ⟨j,z⟩ := v
  by_cases hj : j = 4
  · subst j
    have hc : ((n-1 : ℕ) : C n) = ((n-2 : ℕ) : C n)+1 := by
      have h : n-1 = (n-2)+1 := by omega
      rw [h,Nat.cast_add,Nat.cast_one]
    change adjacent n u (4,z) ↔ adjacent n u (3,z+1)
    unfold adjacent
    by_cases hi : u.1.val < 6
    · simp only [if_pos hi]
      change z-u.2 ∈ shiftSet (u.1.val : C n) (shiftSet ((n-2 : ℕ) : C n) (pSet n)) ↔
        (z+1)-u.2 ∈ shiftSet (u.1.val : C n) (shiftSet ((n-1 : ℕ) : C n) (pSet n))
      rw [mem_shift,mem_shift,mem_shift,mem_shift,hc]
      have he : z-u.2-(u.1.val : C n)-((n-2 : ℕ) : C n) =
          (z+1)-u.2-(u.1.val : C n)-(((n-2 : ℕ) : C n)+1) := by ring
      rw [he]
    · simp only [if_neg hi]
      change z-u.2 ∈ {((n-2 : ℕ) : C n)} ↔ (z+1)-u.2 ∈ {((n-1 : ℕ) : C n)}
      rw [mem_singleton,mem_singleton,hc]
      constructor <;> intro h <;> linear_combination h
  · simp only [canon,if_neg hj]

theorem adjacent_canon (n : ℕ) (hn : 2 ≤ n) (u v : V n) :
    adjacent n u v ↔ adjacent n (canon u) (canon v) :=
  (adjacent_canon_left n u v).trans (adjacent_canon_right n hn (canon u) v)

def Twins (n : ℕ) (u v : V n) : Prop :=
  (∀ w, adjacent n u w ↔ adjacent n v w) ∧
    (∀ w, adjacent n w u ↔ adjacent n w v)

theorem twins_iff_canon (n : ℕ) (hn : 2 ≤ n) (u v : V n) :
    Twins n u v ↔ canon u = canon v := by
  constructor
  · intro h
    apply profiles_determine_canon n hn
    · rw [← outProfile_eq,← outProfile_eq]
      ext t; simpa only [mem_outProfile] using h.1 (3,t)
    · rw [← inProfile_eq n hn,← inProfile_eq n hn]
      ext t; simpa only [mem_inProfile] using h.2 (3,t)
  · intro h
    constructor
    · intro w
      rw [adjacent_canon_left n u w,adjacent_canon_left n v w,h]
    · intro w
      rw [adjacent_canon_right n hn w u,adjacent_canon_right n hn w v,h]

theorem arc_interval (n : ℕ) (x y : C n) :
    x ∈ interval (n+1) (y+1) ↔ tournament (n+1) x y := by
  rw [mem_interval (by dsimp [M]; omega)]
  have he : x-(y+1) = (x-y)-1 := by ring
  rw [he,val_sub_one (by dsimp [M]; omega)]
  by_cases h : x-y = 0
  · rw [if_pos h]
    unfold tournament
    rw [h,ZMod.val_zero]
    dsimp [M]
    omega
  · rw [if_neg h]
    have hp := ZMod.val_pos.mpr h
    unfold tournament
    omega

theorem twin_tournament (n : ℕ) (hn : 2 ≤ n) (t s : C n) :
    adjacent n (3,t) (3,s) ↔ tournament (n+1) t s := by
  rw [← mem_inProfile,inProfile_eq n hn]
  change t ∈ interval (n+1) (s+1) ↔ _
  exact arc_interval n t s

end ByzovPushkarev.Certificate
