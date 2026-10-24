/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode017
import Proofs.RadenkovicGutmanD3Long00StagedUNode118
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e137 : NestedArithmetic.Expr 3 := .times e017 e118
noncomputable def p137 : NestedHorner.Poly 3 := [[[2]]]
theorem step137 : p137=NestedArithmetic.mul p017 p118 := by decide +kernel
#print axioms step137
theorem h137 : NestedArithmetic.compile e137=p137 := StagedExprCompile.compile_times e137 e017 e118 p017 p118 p137 rfl h017 h118 step137
#print axioms h137
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
