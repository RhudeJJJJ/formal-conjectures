/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode030
import Proofs.RadenkovicGutmanD24Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[48],[0]],[[0,0],[0]],[[720,0],[0]],[[0,0],[0]],[[4512,0],[0]],[[0,0],[0]],[[15312,0],[0]],[[0,0],[0]],[[30528,0],[0]],[[0,0],[0]],[[36336,24],[24]],[[0,0],[0]],[[25056,168],[168]],[[0,0],[0]],[[9072,384],[384]],[[0,0],[0]],[[1296,312],[312]],[[0,0],[0]],[[0,72],[72]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
