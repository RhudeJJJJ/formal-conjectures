/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack

namespace Gebendorfer.RadenkovicGutman.InverseNormCompilation
open NestedArithmetic
set_option maxHeartbeats 0

def inverseNorm (a b : NestedHorner.Poly 3) (da db : ℕ) : NestedHorner.Poly 3 :=
  let D := max (da*2) (db*2)
  NestedHorner.add
    (NestedArithmetic.mul (NestedArithmetic.power a 2)
      (NestedArithmetic.power (NestedArithmetic.coordinate 3 0) (D-da*2)))
    (NestedArithmetic.mul (NestedArithmetic.power b 2)
      (NestedArithmetic.power (NestedArithmetic.coordinate 3 0) (D-db*2)))

theorem accepts_power (e : Expr 3) (k : ℕ) (p target : NestedHorner.Poly 3)
    (he : compile (NestedReciprocal.homogenize e).2=p)
    (hp : NestedArithmetic.power p k=target) :
    accepts (NestedReciprocal.homogenize (.pow e k)).2 target=true := by
  unfold accepts
  apply decide_eq_true
  change NestedArithmetic.power (compile (NestedReciprocal.homogenize e).2) k=target
  rw [he]
  exact hp

theorem accepts_norm (a b : Expr 3) (p q target : NestedHorner.Poly 3) (da db : ℕ)
    (ha : compile (NestedReciprocal.homogenize a).2=p)
    (hb : compile (NestedReciprocal.homogenize b).2=q)
    (hda : (NestedReciprocal.homogenize a).1=da)
    (hdb : (NestedReciprocal.homogenize b).1=db)
    (hp : inverseNorm p q da db=target) :
    accepts (NestedReciprocal.homogenize (.plus (.pow a 2) (.pow b 2))).2 target=true := by
  unfold accepts
  apply decide_eq_true
  change NestedHorner.add
    (NestedArithmetic.mul (NestedArithmetic.power (compile (NestedReciprocal.homogenize a).2) 2)
      (NestedArithmetic.power (NestedArithmetic.coordinate 3 0)
        (max ((NestedReciprocal.homogenize a).1*2) ((NestedReciprocal.homogenize b).1*2)-
          (NestedReciprocal.homogenize a).1*2)))
    (NestedArithmetic.mul (NestedArithmetic.power (compile (NestedReciprocal.homogenize b).2) 2)
      (NestedArithmetic.power (NestedArithmetic.coordinate 3 0)
        (max ((NestedReciprocal.homogenize a).1*2) ((NestedReciprocal.homogenize b).1*2)-
          (NestedReciprocal.homogenize b).1*2)))=target
  rw [ha,hb,hda,hdb]
  exact hp

#print axioms accepts_power
#print axioms accepts_norm
end Gebendorfer.RadenkovicGutman.InverseNormCompilation
