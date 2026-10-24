/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedArithmetic

/-!
# Compositional certificates for the existing polynomial program compiler

Each constructor uses already checked child normal forms and one exact arithmetic
identity. The expression equality retains the original program at every step.
-/
namespace Gebendorfer.RadenkovicGutman.StagedExprCompile
open NestedArithmetic

theorem compile_plus (e a b : Expr 3) (p q r : NestedHorner.Poly 3)
    (he : e = .plus a b) (ha : compile a = p) (hb : compile b = q)
    (hr : r = NestedHorner.add p q) : compile e = r :=
  (congrArg compile he).trans ((congrArg₂ NestedHorner.add ha hb).trans hr.symm)

theorem compile_times (e a b : Expr 3) (p q r : NestedHorner.Poly 3)
    (he : e = .times a b) (ha : compile a = p) (hb : compile b = q)
    (hr : r = NestedArithmetic.mul p q) : compile e = r :=
  (congrArg compile he).trans ((congrArg₂ NestedArithmetic.mul ha hb).trans hr.symm)

theorem compile_scaled (c : ℚ) (e a : Expr 3) (p q : NestedHorner.Poly 3)
    (he : e = .scaled c a) (ha : compile a = p)
    (hq : q = NestedHorner.scale c p) : compile e = q :=
  (congrArg compile he).trans ((congrArg (NestedHorner.scale c) ha).trans hq.symm)

theorem compile_pow (k : ℕ) (e a : Expr 3) (p q : NestedHorner.Poly 3)
    (he : e = .pow a k) (ha : compile a = p)
    (hq : q = NestedArithmetic.power p k) : compile e = q :=
  (congrArg compile he).trans ((congrArg (fun p => NestedArithmetic.power p k) ha).trans hq.symm)

theorem compile_of_identity (e source : Expr 3) (p : NestedHorner.Poly 3)
    (he : e = source) (h : compile e = p) : compile source = p :=
  (congrArg compile he.symm).trans h

theorem accepts_of_identity (e source : Expr 3) (p : NestedHorner.Poly 3)
    (he : e = source) (h : compile e = p) : accepts source p = true := by
  unfold accepts
  exact decide_eq_true (compile_of_identity e source p he h)

#print axioms compile_plus
#print axioms compile_times
#print axioms compile_scaled
#print axioms compile_pow
#print axioms compile_of_identity
#print axioms accepts_of_identity
end Gebendorfer.RadenkovicGutman.StagedExprCompile
