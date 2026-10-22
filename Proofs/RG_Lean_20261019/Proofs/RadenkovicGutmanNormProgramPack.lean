/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedClassCell

namespace Gebendorfer.RadenkovicGutman.NormProgramPack
open NestedHorner NestedArithmetic NestedClassPolynomials
set_option maxHeartbeats 0

/-- Six once-checked normal forms, including the exact reciprocal degrees. -/
structure Pack (d : ℚ) (c₁ c₂ : Fin 5) where
  u : NestedHorner.Poly 3
  v : NestedHorner.Poly 3
  j : NestedHorner.Poly 3
  ui : NestedHorner.Poly 3
  vi : NestedHorner.Poly 3
  ji : NestedHorner.Poly 3
  du : ℕ
  dv : ℕ
  dj : ℕ
  hu : compile (programU d c₁ c₂)=u
  hv : compile (programV d c₁ c₂)=v
  hj : compile (programJ d c₁ c₂)=j
  hui : compile (NestedReciprocal.homogenize (programU d c₁ c₂)).2=ui
  hvi : compile (NestedReciprocal.homogenize (programV d c₁ c₂)).2=vi
  hji : compile (NestedReciprocal.homogenize (programJ d c₁ c₂)).2=ji
  hdu : (NestedReciprocal.homogenize (programU d c₁ c₂)).1=du
  hdv : (NestedReciprocal.homogenize (programV d c₁ c₂)).1=dv
  hdj : (NestedReciprocal.homogenize (programJ d c₁ c₂)).1=dj

def polynomial {d : ℚ} {c₁ c₂ : Fin 5} (p : Pack d c₁ c₂)
    (reciprocal : Bool) (s L : ℚ) : NestedHorner.Poly 3 :=
  if reciprocal=true then
    let duv := max p.du p.dv
    let D := max p.dj duv
    add (mul p.ji (power (coordinate 3 0) (D-p.dj)))
      (mul (add (mul (scale (-(L*(1+s))) p.ui) (power (coordinate 3 0) (duv-p.du)))
        (mul (scale (-(L*(1+1/s))) p.vi) (power (coordinate 3 0) (duv-p.dv))))
        (power (coordinate 3 0) (D-duv)))
  else add p.j (add (scale (-(L*(1+s))) p.u) (scale (-(L*(1+1/s))) p.v))

theorem compile_linear (a b c : Expr 3) (A B : ℚ) :
    compile (.plus c (.plus (.scaled A a) (.scaled B b)))=
      add (compile c) (add (scale A (compile a)) (scale B (compile b))) := rfl

theorem compile_inverse_linear (a b c : Expr 3) (A B : ℚ) :
    compile (NestedReciprocal.homogenize (.plus c (.plus (.scaled A a) (.scaled B b)))).2=
      let pa := NestedReciprocal.homogenize a
      let pb := NestedReciprocal.homogenize b
      let pc := NestedReciprocal.homogenize c
      let duv := max pa.1 pb.1
      let D := max pc.1 duv
      add (mul (compile pc.2) (power (coordinate 3 0) (D-pc.1)))
        (mul (add (mul (scale A (compile pa.2)) (power (coordinate 3 0) (duv-pa.1)))
          (mul (scale B (compile pb.2)) (power (coordinate 3 0) (duv-pb.1))))
          (power (coordinate 3 0) (D-duv))) := rfl

theorem accepts_polynomial {d : ℚ} {c₁ c₂ : Fin 5} (p : Pack d c₁ c₂)
    (reciprocal : Bool) (s L : ℚ) :
    NestedArithmetic.accepts (ComputedClassCell.polynomial d c₁ c₂ reciprocal s L)
      (polynomial p reciprocal s L)=true := by
  unfold NestedArithmetic.accepts
  apply decide_eq_true
  by_cases hr : reciprocal=true
  · simp only [ComputedClassCell.polynomial,polynomial,if_pos hr,NestedClassCell.gap]
    rw [compile_inverse_linear]
    dsimp only
    simp only [p.hdu,p.hdv,p.hdj,p.hui,p.hvi,p.hji]
  · simp only [ComputedClassCell.polynomial,polynomial,if_neg hr,NestedClassCell.gap]
    rw [compile_linear,p.hu,p.hv,p.hj]

theorem compile_eq_of_accepts (e : Expr 3) (p : NestedHorner.Poly 3)
    (h : NestedArithmetic.accepts e p=true) : compile e=p := by
  let : DecidableEq (NestedHorner.Poly 3) := polyDecidableEq 3
  exact of_decide_eq_true h

#print axioms accepts_polynomial
#print axioms compile_eq_of_accepts
end Gebendorfer.RadenkovicGutman.NormProgramPack
