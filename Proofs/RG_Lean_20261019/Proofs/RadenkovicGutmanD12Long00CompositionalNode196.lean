/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode195
import Proofs.RadenkovicGutmanD12Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[48,0],[0]],[[0,0],[0]],[[720,0],[0]],[[0,0],[0]],[[4512,0],[0]],[[0,0],[0]],[[15312,0],[0]],[[0,0],[0]],[[30528,0],[0]],[[0,0],[0]],[[36336,24],[24]],[[0,0],[0]],[[25056,168],[168]],[[0,0],[0]],[[9072,384],[384]],[[0,0],[0]],[[1296,312],[312]],[[0,0],[0]],[[0,72],[72]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
