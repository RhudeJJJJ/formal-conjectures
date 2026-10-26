module

public import Proofs.Byzov.Cyclic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-! # The two-sided incidence profiles and their exact fibers

These are the profile sets of Equation (17), in zero-based block indices.
The source bridge is proved separately. Their only repeated profile is the
pair (3,t), (4,t-1); all coordinates and every n>=2 are covered.
-/

@[expose] public section
namespace ByzovPushkarev.Certificate
open Finset

abbrev M (n : ℕ) : ℕ := 2*n+3
instance coordNeZero (n : ℕ) : NeZero (M n) := ⟨by dsimp [M]; omega⟩
abbrev C (n : ℕ) := ZMod (M n)
abbrev V (n : ℕ) := Fin 9 × C n

def canon {n : ℕ} (u : V n) : V n :=
  if u.1 = 4 then (3,u.2+1) else u

def outShape (n : ℕ) (u : V n) : Finset (C n) :=
  if u.1.val < 6 then interval (n+1) (u.2+(u.1.val : C n)+((n-1 : ℕ) : C n))
  else {u.2+((n-1 : ℕ) : C n)}

def inShape (n : ℕ) (u : V n) : Finset (C n) :=
  match u.1.val with
  | 0 => ∅
  | 1 => interval (n+1) (u.2+(n : C n))
  | 2 => interval (n+1) (u.2+((n-1 : ℕ) : C n))
  | 3 => interval (n+1) (u.2+1)
  | 4 => interval (n+1) (u.2+2)
  | 5 => {u.2}
  | 6 => {u.2+((n-1 : ℕ) : C n),u.2+((2*n-1 : ℕ) : C n)}
  | 7 => interval (n+1) (u.2+((n-2 : ℕ) : C n))
  | _ => interval (n+1) (u.2+((n-1 : ℕ) : C n))

@[simp] theorem interval_card (n : ℕ) (a : C n) :
    (interval (n+1) a).card = n+1 := card_interval (by dsimp [M]; omega) a

theorem cast_nat_eq {n a b : ℕ} (ha : a < M n) (hb : b < M n) :
    (a : C n) = (b : C n) ↔ a = b := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv
  · intro h; rw [h]

theorem cast_nat_ne_zero {n a : ℕ} (ha : 0 < a) (ham : a < M n) :
    (a : C n) ≠ 0 := by
  intro h
  have he := (cast_nat_eq ham (show 0 < M n by dsimp [M]; omega)).1 h
  omega

theorem pair_entries_ne (n : ℕ) (hn : 2 ≤ n) (z : C n) :
    z+((n-1 : ℕ) : C n) ≠ z+((2*n-1 : ℕ) : C n) := by
  intro h
  have he := (cast_nat_eq (show n-1 < M n by dsimp [M]; omega)
    (show 2*n-1 < M n by dsimp [M]; omega)).1 (add_left_cancel h)
  omega

theorem outShape_card (n : ℕ) (u : V n) :
    (outShape n u).card = if u.1.val < 6 then n+1 else 1 := by
  by_cases h : u.1.val < 6 <;> simp [outShape,h]

def inCard (n : ℕ) (i : Fin 9) : ℕ :=
  match i.val with | 0 => 0 | 5 => 1 | 6 => 2 | _ => n+1

theorem inShape_card (n : ℕ) (hn : 2 ≤ n) (u : V n) :
    (inShape n u).card = inCard n u.1 := by
  obtain ⟨i,z⟩ := u
  have hpair := pair_entries_ne n hn z
  fin_cases i <;> simp [inShape,inCard,hpair]

theorem profiles_determine_canon (n : ℕ) (hn : 2 ≤ n) (u v : V n)
    (hout : outShape n u = outShape n v) (hin : inShape n u = inShape n v) :
    canon u = canon v := by
  obtain ⟨i,z⟩ := u
  obtain ⟨j,w⟩ := v
  have hco := congrArg Finset.card hout
  have hci := congrArg Finset.card hin
  rw [outShape_card,outShape_card] at hco
  rw [inShape_card n hn,inShape_card n hn] at hci
  have hq0 : 0 < n+1 := by omega
  have hqm : n+1 < M n := by dsimp [M]; omega
  have hc1 : ((n-1 : ℕ) : C n) = (n : C n)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have h2 : (2 : C n) ≠ 0 := cast_nat_ne_zero (by decide) (by dsimp [M]; omega)
  have hq : ((n+1 : ℕ) : C n) ≠ 0 := cast_nat_ne_zero (by omega) (by dsimp [M]; omega)
  have hn1 : ((n-1 : ℕ) : C n) ≠ 0 := cast_nat_ne_zero (by omega) (by dsimp [M]; omega)
  fin_cases i <;> fin_cases j
  · -- Block indices 0, 0.
    change interval (n+1) (z+(0 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(0 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    have hz : z = w := by linear_combination ho
    subst w
    rfl
  · -- Block indices 0, 1.
    norm_num [inCard] at hco hci
  · -- Block indices 0, 2.
    norm_num [inCard] at hco hci
  · -- Block indices 0, 3.
    norm_num [inCard] at hco hci
  · -- Block indices 0, 4.
    norm_num [inCard] at hco hci
  · -- Block indices 0, 5.
    norm_num [inCard] at hco hci
  · -- Block indices 0, 6.
    norm_num [inCard] at hco hci
  · -- Block indices 0, 7.
    norm_num [inCard] at hco hci
  · -- Block indices 0, 8.
    norm_num [inCard] at hco hci
  · -- Block indices 1, 0.
    norm_num [inCard] at hco hci
  · -- Block indices 1, 1.
    change interval (n+1) (z+(1 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(1 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    have hz : z = w := by linear_combination ho
    subst w
    rfl
  · -- Block indices 1, 2.
    change interval (n+1) (z+(1 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(2 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+(n : C n)) = interval (n+1) (w+((n-1 : ℕ) : C n)) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    rw [hc1] at hi
    apply False.elim
    apply h2
    linear_combination (hi-ho)
  · -- Block indices 1, 3.
    change interval (n+1) (z+(1 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(3 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+(n : C n)) = interval (n+1) (w+1) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    apply False.elim
    apply hq
    rw [Nat.cast_add,Nat.cast_one]
    linear_combination (hi-ho)
  · -- Block indices 1, 4.
    change interval (n+1) (z+(1 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(4 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+(n : C n)) = interval (n+1) (w+2) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    apply False.elim
    apply hq
    rw [Nat.cast_add,Nat.cast_one]
    linear_combination (hi-ho)
  · -- Block indices 1, 5.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 1, 6.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 1, 7.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 1, 8.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 2, 0.
    norm_num [inCard] at hco hci
  · -- Block indices 2, 1.
    change interval (n+1) (z+(2 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(1 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+((n-1 : ℕ) : C n)) = interval (n+1) (w+(n : C n)) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    rw [hc1] at hi
    apply False.elim
    apply h2
    linear_combination -(hi-ho)
  · -- Block indices 2, 2.
    change interval (n+1) (z+(2 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(2 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    have hz : z = w := by linear_combination ho
    subst w
    rfl
  · -- Block indices 2, 3.
    change interval (n+1) (z+(2 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(3 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+((n-1 : ℕ) : C n)) = interval (n+1) (w+1) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    rw [hc1] at hi
    apply False.elim
    apply hn1
    rw [hc1]
    linear_combination (hi-ho)
  · -- Block indices 2, 4.
    change interval (n+1) (z+(2 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(4 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+((n-1 : ℕ) : C n)) = interval (n+1) (w+2) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    rw [hc1] at hi
    apply False.elim
    apply hn1
    rw [hc1]
    linear_combination (hi-ho)
  · -- Block indices 2, 5.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 2, 6.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 2, 7.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 2, 8.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 3, 0.
    norm_num [inCard] at hco hci
  · -- Block indices 3, 1.
    change interval (n+1) (z+(3 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(1 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+1) = interval (n+1) (w+(n : C n)) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    apply False.elim
    apply hq
    rw [Nat.cast_add,Nat.cast_one]
    linear_combination -(hi-ho)
  · -- Block indices 3, 2.
    change interval (n+1) (z+(3 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(2 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+1) = interval (n+1) (w+((n-1 : ℕ) : C n)) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    rw [hc1] at hi
    apply False.elim
    apply hn1
    rw [hc1]
    linear_combination -(hi-ho)
  · -- Block indices 3, 3.
    change interval (n+1) (z+(3 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(3 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    have hz : z = w := by linear_combination ho
    subst w
    rfl
  · -- Block indices 3, 4.
    change interval (n+1) (z+(3 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(4 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    have hz : z = w+1 := by linear_combination ho
    change ((3 : Fin 9),z) = ((3 : Fin 9),w+1)
    exact Prod.ext rfl hz
  · -- Block indices 3, 5.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 3, 6.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 3, 7.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 3, 8.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 4, 0.
    norm_num [inCard] at hco hci
  · -- Block indices 4, 1.
    change interval (n+1) (z+(4 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(1 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+2) = interval (n+1) (w+(n : C n)) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    apply False.elim
    apply hq
    rw [Nat.cast_add,Nat.cast_one]
    linear_combination -(hi-ho)
  · -- Block indices 4, 2.
    change interval (n+1) (z+(4 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(2 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    change interval (n+1) (z+2) = interval (n+1) (w+((n-1 : ℕ) : C n)) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    rw [hc1] at hi
    apply False.elim
    apply hn1
    rw [hc1]
    linear_combination -(hi-ho)
  · -- Block indices 4, 3.
    change interval (n+1) (z+(4 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(3 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    have hz : z+1 = w := by linear_combination ho
    change ((3 : Fin 9),z+1) = ((3 : Fin 9),w)
    exact Prod.ext rfl hz
  · -- Block indices 4, 4.
    change interval (n+1) (z+(4 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(4 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    have hz : z = w := by linear_combination ho
    subst w
    rfl
  · -- Block indices 4, 5.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 4, 6.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 4, 7.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 4, 8.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 5, 0.
    norm_num [inCard] at hco hci
  · -- Block indices 5, 1.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 5, 2.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 5, 3.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 5, 4.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 5, 5.
    change interval (n+1) (z+(5 : C n)+((n-1 : ℕ) : C n)) =
      interval (n+1) (w+(5 : C n)+((n-1 : ℕ) : C n)) at hout
    have ho := (interval_eq_iff hq0 hqm _ _).1 hout
    have hz : z = w := by linear_combination ho
    subst w
    rfl
  · -- Block indices 5, 6.
    norm_num [inCard] at hco hci
  · -- Block indices 5, 7.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 5, 8.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 6, 0.
    norm_num [inCard] at hco hci
  · -- Block indices 6, 1.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 6, 2.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 6, 3.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 6, 4.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 6, 5.
    norm_num [inCard] at hco hci
  · -- Block indices 6, 6.
    change {z+((n-1 : ℕ) : C n)} = {w+((n-1 : ℕ) : C n)} at hout
    have hz : z = w := add_right_cancel (singleton_injective hout)
    subst w
    rfl
  · -- Block indices 6, 7.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 6, 8.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 7, 0.
    norm_num [inCard] at hco hci
  · -- Block indices 7, 1.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 7, 2.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 7, 3.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 7, 4.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 7, 5.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 7, 6.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 7, 7.
    change {z+((n-1 : ℕ) : C n)} = {w+((n-1 : ℕ) : C n)} at hout
    have hz : z = w := add_right_cancel (singleton_injective hout)
    subst w
    rfl
  · -- Block indices 7, 8.
    change {z+((n-1 : ℕ) : C n)} = {w+((n-1 : ℕ) : C n)} at hout
    have hz : z = w := add_right_cancel (singleton_injective hout)
    subst w
    change interval (n+1) (z+((n-2 : ℕ) : C n)) = interval (n+1) (z+((n-1 : ℕ) : C n)) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    have he := (cast_nat_eq (show n-2 < M n by dsimp [M]; omega)
      (show n-1 < M n by dsimp [M]; omega)).1 (add_left_cancel hi)
    omega
  · -- Block indices 8, 0.
    norm_num [inCard] at hco hci
  · -- Block indices 8, 1.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 8, 2.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 8, 3.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 8, 4.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 8, 5.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 8, 6.
    norm_num [inCard] at hco hci
    omega
  · -- Block indices 8, 7.
    change {z+((n-1 : ℕ) : C n)} = {w+((n-1 : ℕ) : C n)} at hout
    have hz : z = w := add_right_cancel (singleton_injective hout)
    subst w
    change interval (n+1) (z+((n-1 : ℕ) : C n)) = interval (n+1) (z+((n-2 : ℕ) : C n)) at hin
    have hi := (interval_eq_iff hq0 hqm _ _).1 hin
    have he := (cast_nat_eq (show n-1 < M n by dsimp [M]; omega)
      (show n-2 < M n by dsimp [M]; omega)).1 (add_left_cancel hi)
    omega
  · -- Block indices 8, 8.
    change {z+((n-1 : ℕ) : C n)} = {w+((n-1 : ℕ) : C n)} at hout
    have hz : z = w := add_right_cancel (singleton_injective hout)
    subst w
    rfl

end ByzovPushkarev.Certificate
