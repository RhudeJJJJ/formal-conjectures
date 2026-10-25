/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedIntegerAffine

namespace Gebendorfer.RadenkovicGutman.PowerBernstein
open NestedInteger
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def Bounded : (n : ℕ) → (Fin n → ℕ) → Poly n → Prop
  | 0, _, _ => True
  | n+1, d, p => p.length ≤ d 0+1 ∧ ∀ c ∈ p, Bounded n (fun i => d i.succ) c

def Safe (n : ℕ) (d : Fin n → ℕ) (p : Poly n) : Prop :=
  Bounded n d p ∧ powerCheck n p=true

theorem length_zipAdd {A : Type*} (f : A → A → A) (p q : List A) :
    (NestedHorner.zipAdd f p q).length=max p.length q.length := by
  induction p generalizing q with
  | nil => simp [NestedHorner.zipAdd]
  | cons c p ih =>
    cases q with
    | nil => simp [NestedHorner.zipAdd]
    | cons e q =>
      simp only [NestedHorner.zipAdd,List.length_cons,ih]
      omega

theorem zero_safe (n : ℕ) (d : Fin n → ℕ) : Safe n d (zero n) := by
  cases n <;> simp [Safe,Bounded,zero,powerCheck]

theorem scale_safe (n : ℕ) (d : Fin n → ℕ) (c : ℤ) (hc : 0≤c)
    (p : Poly n) (hp : Safe n d p) : Safe n d (scale c p) := by
  induction n with
  | zero =>
    exact ⟨True.intro,decide_eq_true (mul_nonneg hc (of_decide_eq_true hp.2))⟩
  | succ n ih =>
    obtain ⟨⟨hl,hb⟩,hpos⟩ := hp
    have hs : ∀ a ∈ p.map (scale c), Safe n (fun i => d i.succ) a := by
      intro a ha
      obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp ha
      exact ih (fun i => d i.succ) b
        ⟨hb b hbmem,List.all_eq_true.mp hpos b hbmem⟩
    exact ⟨⟨by simpa only [scale,List.length_map] using hl,
      fun a ha => (hs a ha).1⟩,List.all_eq_true.mpr (fun a ha => (hs a ha).2)⟩

theorem add_safe (n : ℕ) (d : Fin n → ℕ) (p q : Poly n)
    (hp : Safe n d p) (hq : Safe n d q) : Safe n d (add p q) := by
  induction n with
  | zero =>
    exact ⟨True.intro,decide_eq_true (add_nonneg
      (of_decide_eq_true hp.2) (of_decide_eq_true hq.2))⟩
  | succ n ih =>
    induction p generalizing q with
    | nil => simpa only [add,NestedHorner.zipAdd] using hq
    | cons c p ihp =>
      cases q with
      | nil => simpa only [add,NestedHorner.zipAdd] using hp
      | cons e q =>
        have hpc : powerCheck n c=true ∧ p.all (powerCheck n)=true := by
          simpa only [powerCheck,List.all_cons,Bool.and_eq_true] using hp.2
        have hqc : powerCheck n e=true ∧ q.all (powerCheck n)=true := by
          simpa only [powerCheck,List.all_cons,Bool.and_eq_true] using hq.2
        have ht : Safe (n+1) d p := ⟨⟨by
            have := hp.1.1
            simp only [List.length_cons] at this
            omega,
          fun a ha => hp.1.2 a (List.mem_cons_of_mem c ha)⟩,hpc.2⟩
        have hu : Safe (n+1) d q := ⟨⟨by
            have := hq.1.1
            simp only [List.length_cons] at this
            omega,
          fun a ha => hq.1.2 a (List.mem_cons_of_mem e ha)⟩,hqc.2⟩
        have htail := ihp q ht hu
        have hhead := ih (fun i => d i.succ) c e
          ⟨hp.1.2 c (List.mem_cons_self),hpc.1⟩
          ⟨hq.1.2 e (List.mem_cons_self),hqc.1⟩
        constructor
        · constructor
          · change (NestedHorner.zipAdd _ (c::p) (e::q)).length ≤ _
            rw [length_zipAdd]
            exact max_le hp.1.1 hq.1.1
          · intro a ha
            change a ∈ add (n := n) c e :: add (n := n+1) p q at ha
            rcases List.mem_cons.mp ha with he | he
            · subst a; exact hhead.1
            · exact htail.1.2 a he
        · change (add (n := n) c e :: add (n := n+1) p q).all (powerCheck n)=true
          simpa only [powerCheck,List.all_cons,Bool.and_eq_true] using And.intro hhead.2 htail.2

theorem coefficient_safe (n : ℕ) (d : Fin n → ℕ) (D j k : ℕ)
    (p : Poly (n+1)) (hp : ∀ c ∈ p, Safe n d c) :
    Safe n d (coefficientFrom D j k p) := by
  induction p generalizing k with
  | nil => exact zero_safe n d
  | cons c p ih =>
    have htail := ih (k+1) (fun a ha => hp a (List.mem_cons_of_mem c ha))
    by_cases h : k≤j
    · simp only [coefficientFrom,if_pos h]
      exact add_safe n d _ _
        (scale_safe n d _ (Int.natCast_nonneg _) c (hp c List.mem_cons_self)) htail
    · simp only [coefficientFrom,if_neg h]
      exact add_safe n d _ _ (zero_safe n d) htail

theorem bernstein_of_safe (n : ℕ) (d : Fin n → ℕ) (p : Poly n)
    (hp : Safe n d p) : bernsteinCheck n d p=true := by
  induction n with
  | zero => exact hp.2
  | succ n ih =>
    apply decide_eq_true
    refine ⟨hp.1.1,?_⟩
    intro j
    apply ih
    exact coefficient_safe n (fun i => d i.succ) (d 0) j.val 0 p
      (fun c hc => ⟨hp.1.2 c hc,List.all_eq_true.mp hp.2 c hc⟩)

theorem bounded_of_rectangular (n : ℕ) (d : Fin n → ℕ) (p : Poly n)
    (hp : rectangular n d p=true) : Bounded n d p := by
  induction n with
  | zero => exact True.intro
  | succ n ih =>
    have h : p.length=d 0+1 ∧ p.all (rectangular n (fun i => d i.succ))=true := by
      simpa only [rectangular,Bool.and_eq_true,decide_eq_true_eq] using hp
    exact ⟨h.1.le,fun c hc => ih _ c (List.all_eq_true.mp h.2 c hc)⟩

/-- Nonnegative power coefficients suffice for the existing Bernstein checker;
the complete rectangular degree hypothesis remains required. -/
theorem checked (n : ℕ) (d : Fin n → ℕ) (p : Poly n)
    (hr : rectangular n d p=true) (hp : powerCheck n p=true) :
    bernsteinCheck n d p=true :=
  bernstein_of_safe n d p ⟨bounded_of_rectangular n d p hr,hp⟩

#print axioms checked
#print axioms coefficient_safe
#print axioms add_safe
#print axioms scale_safe
end Gebendorfer.RadenkovicGutman.PowerBernstein
