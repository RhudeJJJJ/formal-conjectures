/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode194
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e120
noncomputable def p195 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[40,0],[0,0]],[[0,0],[0,0]],[[338,0],[0,0]],[[0,0],[0,0]],[[1578,0],[0,0]],[[0,0],[0,0]],[[4462,0],[0,0]],[[0,0],[0,0]],[[7872,2],[2,0]],[[0,0],[0,0]],[[8596,22],[22,0]],[[0,0],[0,0]],[[5538,88],[88,0]],[[0,0],[0,0]],[[1852,156],[156,0]],[[0,0],[0,0]],[[204,118],[118,0]],[[0,0],[0,0]],[[-18,30],[30,2]],[[0],[0,0]],[[0],[0,2]]]
theorem step195 : p195=NestedArithmetic.mul p194 p120 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e120 p194 p120 p195 rfl h194 h120 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
