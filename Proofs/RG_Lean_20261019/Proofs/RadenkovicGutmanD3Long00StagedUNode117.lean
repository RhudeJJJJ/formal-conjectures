/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode017
import Proofs.RadenkovicGutmanD3Long00StagedUNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .times e017 e006
noncomputable def p117 : NestedHorner.Poly 3 := [[[2]]]
theorem step117 : p117=NestedArithmetic.mul p017 p006 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_times e117 e017 e006 p017 p006 p117 rfl h017 h006 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
