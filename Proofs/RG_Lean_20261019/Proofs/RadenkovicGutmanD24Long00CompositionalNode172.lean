/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode171
import Proofs.RadenkovicGutmanD24Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[48,0],[0]],[[0,0],[0]],[[720,0],[0]],[[0,0],[0]],[[4512,0],[0]],[[0,0],[0]],[[15312,0],[0]],[[0,0],[0]],[[30528,0],[0]],[[0,0],[0]],[[36336,24],[24]],[[0,0],[0]],[[25056,168],[168]],[[0,0],[0]],[[9072,384],[384]],[[0,0],[0]],[[1296,312],[312]],[[0,0],[0]],[[0,72],[72]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
