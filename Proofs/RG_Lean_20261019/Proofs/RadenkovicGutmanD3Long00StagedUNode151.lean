/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode006
import Proofs.RadenkovicGutmanD3Long00StagedUNode127
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e151 : NestedArithmetic.Expr 3 := .times e006 e127
noncomputable def p151 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step151 : p151=NestedArithmetic.mul p006 p127 := by decide +kernel
#print axioms step151
theorem h151 : NestedArithmetic.compile e151=p151 := StagedExprCompile.compile_times e151 e006 e127 p006 p127 p151 rfl h006 h127 step151
#print axioms h151
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
