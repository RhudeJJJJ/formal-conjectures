/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode194
import Proofs.RadenkovicGutmanD44Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[176],[0]],[[0,0],[0]],[[2640,0],[0]],[[0,0],[0]],[[16544,0],[0]],[[0,0],[0]],[[56144,0],[0]],[[0,0],[0]],[[111936,0],[0]],[[0,0],[0]],[[133232,88],[88]],[[0,0],[0]],[[91872,616],[616]],[[0,0],[0]],[[33264,1408],[1408]],[[0,0],[0]],[[4752,1144],[1144]],[[0,0],[0]],[[0,264],[264]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
