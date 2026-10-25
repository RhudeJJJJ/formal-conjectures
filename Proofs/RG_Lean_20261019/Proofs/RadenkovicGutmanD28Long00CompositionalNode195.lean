/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode194
import Proofs.RadenkovicGutmanD28Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[112],[0]],[[0,0],[0]],[[1680,0],[0]],[[0,0],[0]],[[10528,0],[0]],[[0,0],[0]],[[35728,0],[0]],[[0,0],[0]],[[71232,0],[0]],[[0,0],[0]],[[84784,56],[56]],[[0,0],[0]],[[58464,392],[392]],[[0,0],[0]],[[21168,896],[896]],[[0,0],[0]],[[3024,728],[728]],[[0,0],[0]],[[0,168],[168]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
