/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode009
import Proofs.RadenkovicGutmanD3Long00StagedUNode118
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e129 : NestedArithmetic.Expr 3 := .times e009 e118
noncomputable def p129 : NestedHorner.Poly 3 := [[[4]]]
theorem step129 : p129=NestedArithmetic.mul p009 p118 := by decide +kernel
#print axioms step129
theorem h129 : NestedArithmetic.compile e129=p129 := StagedExprCompile.compile_times e129 e009 e118 p009 p118 p129 rfl h009 h118 step129
#print axioms h129
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
