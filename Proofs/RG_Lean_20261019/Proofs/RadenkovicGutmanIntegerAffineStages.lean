/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerNormProgramPack

namespace Gebendorfer.RadenkovicGutman.IntegerAffineStages

def inner (raw : NestedInteger.Poly 3) (l w D : Fin 3 → ℤ) : NestedInteger.Poly 3 :=
  raw.map (fun c => NestedInteger.clearedAll 2 c
    (fun i => l i.succ) (fun i => w i.succ) (fun i => D i.succ))

theorem checked (raw b a : NestedInteger.Poly 3) (l w D : Fin 3 → ℤ)
    (hb : b=inner raw l w D)
    (ha : a=NestedInteger.clearedOuter (l 0) (w 0) (D 0) b) :
    a=NestedInteger.clearedAll 3 raw l w D := by
  rw [ha,hb]
  rfl

#print axioms checked
end Gebendorfer.RadenkovicGutman.IntegerAffineStages
