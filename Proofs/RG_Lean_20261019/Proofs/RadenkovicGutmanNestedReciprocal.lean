/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedArithmetic

namespace Gebendorfer.RadenkovicGutman.NestedReciprocal
open NestedArithmetic
set_option maxHeartbeats 0

/-- Clear exactly a sufficient power of the first coordinate, retaining all
other parameters. The transform is a computable rational polynomial program. -/
def homogenize {n : ℕ} : Expr (n+1) → ℕ × Expr (n+1)
  | .rational c => (0,.rational c)
  | .indet i => if i=0 then (1,.rational 1) else (0,.indet i)
  | .plus a b =>
    let pa := homogenize a; let pb := homogenize b
    let d := max pa.1 pb.1
    (d,.plus (.times pa.2 (.pow (.indet 0) (d-pa.1)))
      (.times pb.2 (.pow (.indet 0) (d-pb.1))))
  | .times a b =>
    let pa := homogenize a; let pb := homogenize b
    (pa.1+pb.1,.times pa.2 pb.2)
  | .scaled c a =>
    let pa := homogenize a
    (pa.1,.scaled c pa.2)
  | .pow a k =>
    let pa := homogenize a
    (pa.1*k,.pow pa.2 k)

noncomputable section
def invert {n : ℕ} (x : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  fun i => if i=0 then 1/x 0 else x i

@[simp] theorem invert_zero {n : ℕ} (x : Fin (n+1) → ℝ) : invert x 0=1/x 0 := by
  simp [invert]

theorem invert_other {n : ℕ} (x : Fin (n+1) → ℝ) (i : Fin (n+1)) (hi : i ≠ 0) :
    invert x i=x i := by simp [invert,hi]

theorem homogenize_sound {n : ℕ} (e : Expr (n+1)) (x : Fin (n+1) → ℝ) (hx : x 0 ≠ 0) :
    value (homogenize e).2 x=x 0^(homogenize e).1*value e (invert x) := by
  induction e with
  | rational c => simp [homogenize,value]
  | indet i =>
    by_cases hi : i=0
    · subst i
      simp [homogenize,value,hx]
    · simp [homogenize,value,invert,hi]
  | plus a b ha hb =>
    have hpa : x 0^(homogenize a).1*x 0^(max (homogenize a).1 (homogenize b).1-(homogenize a).1)=
        x 0^max (homogenize a).1 (homogenize b).1 := by
      rw [← pow_add,Nat.add_sub_of_le (Nat.le_max_left _ _)]
    have hpb : x 0^(homogenize b).1*x 0^(max (homogenize a).1 (homogenize b).1-(homogenize b).1)=
        x 0^max (homogenize a).1 (homogenize b).1 := by
      rw [← pow_add,Nat.add_sub_of_le (Nat.le_max_right _ _)]
    simp only [homogenize,value]
    rw [ha,hb]
    calc
      _ = (x 0^(homogenize a).1*x 0^(max (homogenize a).1 (homogenize b).1-(homogenize a).1))*value a (invert x)+
        (x 0^(homogenize b).1*x 0^(max (homogenize a).1 (homogenize b).1-(homogenize b).1))*value b (invert x) := by ring
      _ = _ := by rw [hpa,hpb]; ring
  | times a b ha hb =>
    simp only [homogenize,value,ha,hb,pow_add]
    ring
  | scaled c a ha =>
    simp only [homogenize,value,ha]
    ring
  | pow a k ha =>
    simp only [homogenize,value,ha,mul_pow,pow_mul]

theorem nonneg_of_homogenize {n : ℕ} (e : Expr (n+1)) (x : Fin (n+1) → ℝ)
    (hx : 0 < x 0) (h : 0 ≤ value (homogenize e).2 x) : 0 ≤ value e (invert x) := by
  rw [homogenize_sound e x hx.ne'] at h
  have hc : x 0^(homogenize e).1*0 ≤ x 0^(homogenize e).1*value e (invert x) := by
    simpa only [mul_zero] using h
  exact (mul_le_mul_iff_right₀ (pow_pos hx _)).mp hc

#print axioms invert_zero
#print axioms invert_other
#print axioms homogenize_sound
#print axioms nonneg_of_homogenize
end
end Gebendorfer.RadenkovicGutman.NestedReciprocal
