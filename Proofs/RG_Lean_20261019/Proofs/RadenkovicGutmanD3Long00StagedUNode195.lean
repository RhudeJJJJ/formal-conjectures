/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode194
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e120
noncomputable def p195 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[45,0],[0,0]],[[0,0],[0,0]],[[413,0],[0,0]],[[0,0],[0,0]],[[2048,0],[0,0]],[[0,0],[0,0]],[[6057,0],[0,0]],[[0,0],[0,0]],[[11052,2],[2,0]],[[0,0],[0,0]],[[12380,25],[25,0]],[[0,0],[0,0]],[[8140,110],[110,0]],[[0,0],[0,0]],[[2775,210],[210,0]],[[0,0],[0,0]],[[315,168],[168,0]],[[0,0],[0,0]],[[-27,45],[45,2]],[[0],[0,0]],[[0],[0,3]]]
theorem step195 : p195=NestedArithmetic.mul p194 p120 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e120 p194 p120 p195 rfl h194 h120 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
