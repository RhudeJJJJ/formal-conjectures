/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e144 : NestedArithmetic.Expr 3 := .pow e000 10
noncomputable def p144 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[1]]]
theorem step144 : p144=NestedArithmetic.power p000 10 := by decide +kernel
#print axioms step144
theorem h144 : NestedArithmetic.compile e144=p144 := StagedExprCompile.compile_pow 10 e144 e000 p000 p144 rfl h000 step144
#print axioms h144
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
