/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode142
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e143 : NestedArithmetic.Expr 3 := .times e142 e120
noncomputable def p143 : NestedHorner.Poly 3 := [[[1]],[[0]],[[8]],[[0]],[[22]],[[0]],[[24]],[[0]],[[9]]]
theorem step143 : p143=NestedArithmetic.mul p142 p120 := by decide +kernel
#print axioms step143
theorem h143 : NestedArithmetic.compile e143=p143 := StagedExprCompile.compile_times e143 e142 e120 p142 p120 p143 rfl h142 h120 step143
#print axioms h143
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
