module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Ring

/-! # Cyclic intervals and their intrinsic directed cycle

The consecutive half-interval tournament in Byzov--Pushkarev Conjecture 8
has a definable predecessor: it dominates all other out-neighbors.
This proves rotation rigidity without a counting assumption.
-/

@[expose] public section
namespace ByzovPushkarev.Certificate
open Finset
variable {m : ℕ} [NeZero m]

def interval (q : ℕ) (a : ZMod m) : Finset (ZMod m) :=
  (range q).image fun (k : ℕ) => a + (k : ZMod m)

theorem mem_interval {q : ℕ} (hq : q ≤ m) (a x : ZMod m) :
    x ∈ interval q a ↔ (x-a).val < q := by
  constructor
  · intro hx
    obtain ⟨k, hk, h⟩ := mem_image.1 hx
    have hkq := mem_range.1 hk
    have hkm : k < m := lt_of_lt_of_le hkq hq
    rw [← h, add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hkm]
    exact hkq
  · intro hx
    refine mem_image.2 ⟨(x-a).val, mem_range.2 hx, ?_⟩
    rw [ZMod.natCast_zmod_val]
    ring

omit [NeZero m] in
theorem card_interval {q : ℕ} (hq : q ≤ m) (a : ZMod m) :
    (interval q a).card = q := by
  rw [interval, card_image_of_injOn]
  · exact card_range q
  · intro i hi j hj he
    have h := congrArg ZMod.val (add_left_cancel he)
    rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (mem_range.1 hi) hq),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (mem_range.1 hj) hq)] at h
    exact h

theorem val_sub_one (hm : 1 < m) (x : ZMod m) :
    (x-1).val = if x = 0 then m-1 else x.val-1 := by
  have h1 : (1 : ZMod m).val = 1 := ZMod.val_one'' (by omega)
  by_cases hx : x = 0
  · subst x
    have h10 : (1 : ZMod m) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [h1,ZMod.val_zero] at hv
      omega
    simp [ZMod.neg_val,h10,h1]
  · rw [if_neg hx, ZMod.val_sub (by have := ZMod.val_pos.mpr hx; omega), h1]

theorem interval_boundary {q : ℕ} (hq0 : 0 < q) (hqm : q < m) (a x : ZMod m) :
    (x ∈ interval q a ∧ x-1 ∉ interval q a) ↔ x = a := by
  rw [mem_interval (le_of_lt hqm), mem_interval (le_of_lt hqm)]
  have he : x-1-a = (x-a)-1 := by ring
  rw [he, val_sub_one (by omega)]
  by_cases hx : x-a = 0
  · rw [if_pos hx, hx, ZMod.val_zero]
    constructor
    · intro _; exact sub_eq_zero.mp hx
    · intro _; exact ⟨hq0,by omega⟩
  · rw [if_neg hx]
    have hpos := ZMod.val_pos.mpr hx
    constructor
    · intro h; exfalso; have := h.1; have := h.2; omega
    · intro h; exact False.elim (hx (sub_eq_zero.mpr h))

theorem interval_eq_iff {q : ℕ} (hq0 : 0 < q) (hqm : q < m) (a b : ZMod m) :
    interval q a = interval q b ↔ a = b := by
  constructor
  · intro h
    have ha := (interval_boundary hq0 hqm a a).2 rfl
    rw [h] at ha
    exact (interval_boundary hq0 hqm b a).1 ha
  · rintro rfl; rfl

theorem val_reflection {q : ℕ} (hq0 : 0 < q) (hqm : q ≤ m) (x : ZMod m) :
    x.val < q ↔ (((q-1 : ℕ) : ZMod m)-x).val < q := by
  have hc : (((q-1 : ℕ) : ZMod m)).val = q-1 := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega)]
  have forward : ∀ y : ZMod m, y.val < q → (((q-1 : ℕ) : ZMod m)-y).val < q := by
    intro y hy
    rw [ZMod.val_sub (by rw [hc]; omega),hc]
    omega
  constructor
  · exact forward x
  · intro h
    have hh := forward (((q-1 : ℕ) : ZMod m)-x) h
    have he : ((q-1 : ℕ) : ZMod m)-(((q-1 : ℕ) : ZMod m)-x) = x := by ring
    rwa [he] at hh

theorem interval_reflection {q : ℕ} (hq0 : 0 < q) (hqm : q ≤ m)
    (a z x : ZMod m) :
    z-x ∈ interval q a ↔ x ∈ interval q (z-a-((q-1 : ℕ) : ZMod m)) := by
  rw [mem_interval hqm,mem_interval hqm]
  have he : x-(z-a-((q-1 : ℕ) : ZMod m)) =
      ((q-1 : ℕ) : ZMod m)-((z-x)-a) := by ring
  rw [he]
  exact val_reflection hq0 hqm _

def tournament (q : ℕ) (x y : ZMod m) : Prop :=
  0 < (x-y).val ∧ (x-y).val ≤ q

omit [NeZero m] in
theorem predecessor_arc {q : ℕ} (hq : 0 < q) (hm : m = 2*q+1) (x : ZMod m) :
    tournament q x (x-1) := by
  have h1 : (1 : ZMod m).val = 1 := ZMod.val_one'' (by omega)
  have he : x-(x-1) = (1 : ZMod m) := by ring
  simp only [tournament, he, h1]
  omega

theorem predecessor_characterization {q : ℕ} (hq : 0 < q) (hm : m = 2*q+1)
    (x y : ZMod m) :
    (tournament q x y ∧
      ∀ z, tournament q x z → z ≠ y → tournament q y z) ↔ y = x-1 := by
  have hmlt : 1 < m := by omega
  constructor
  · rintro ⟨hxy, hsource⟩
    by_contra hne
    have hbad := hsource (x-1) (predecessor_arc hq hm x) (Ne.symm hne)
    have hd : 1 < (x-y).val := by
      have hd0 := hxy.1
      by_contra h
      have he : (x-y).val = (1 : ZMod m).val := by rw [ZMod.val_one'' (by omega)]; omega
      have heq := ZMod.val_injective m he
      apply hne
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp heq).symm
    have hzero : (x-y)-1 ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [val_sub_one hmlt, if_neg (by intro he; rw [he, ZMod.val_zero] at hd; omega), ZMod.val_zero] at hv
      omega
    have he : y-(x-1) = -((x-y)-1) := by ring
    rw [tournament, he, ZMod.neg_val, if_neg hzero, val_sub_one hmlt,
      if_neg (by intro h; rw [h, ZMod.val_zero] at hd; omega)] at hbad
    have := hxy.2
    omega
  · rintro rfl
    refine ⟨predecessor_arc hq hm x, ?_⟩
    intro z hxz hne
    have hd : 1 < (x-z).val := by
      have hd0 := hxz.1
      by_contra h
      have he : (x-z).val = (1 : ZMod m).val := by rw [ZMod.val_one'' (by omega)]; omega
      have heq := ZMod.val_injective m he
      apply hne
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp heq).symm
    have he : (x-1)-z = (x-z)-1 := by ring
    rw [tournament, he, val_sub_one hmlt,
      if_neg (by intro h; rw [h, ZMod.val_zero] at hd; omega)]
    have := hxz.2
    omega

theorem tournament_rotation {q : ℕ} (hq : 0 < q) (hm : m = 2*q+1)
    (e : ZMod m ≃ ZMod m)
    (he : ∀ x y, tournament q (e x) (e y) ↔ tournament q x y) :
    ∀ x, e x = e 0 + x := by
  have hp : ∀ x, e (x-1) = e x-1 := by
    intro x
    apply (predecessor_characterization hq hm (e x) (e (x-1))).1
    refine ⟨(he _ _).2 (predecessor_arc hq hm x), ?_⟩
    intro z hz hzne
    obtain ⟨w, rfl⟩ := e.surjective z
    apply (he _ _).2
    have hw : w ≠ x-1 := by intro h; apply hzne; rw [h]
    exact ((predecessor_characterization hq hm x (x-1)).2 rfl).2 w ((he _ _).1 hz) hw
  have hs : ∀ x, e (x+1) = e x+1 := by
    intro x
    have h := hp (x+1)
    rw [add_sub_cancel_right] at h
    exact (eq_sub_iff_add_eq.mp h).symm
  have hn : ∀ k : ℕ, e (k : ZMod m) = e 0 + (k : ZMod m) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, hs, ih, add_assoc]
  intro x
  simpa only [ZMod.natCast_zmod_val] using hn x.val

end ByzovPushkarev.Certificate
