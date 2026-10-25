/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode195
import Proofs.RadenkovicGutmanD28Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[112,0],[0]],[[0,0],[0]],[[1680,0],[0]],[[0,0],[0]],[[10528,0],[0]],[[0,0],[0]],[[35728,0],[0]],[[0,0],[0]],[[71232,0],[0]],[[0,0],[0]],[[84784,56],[56]],[[0,0],[0]],[[58464,392],[392]],[[0,0],[0]],[[21168,896],[896]],[[0,0],[0]],[[3024,728],[728]],[[0,0],[0]],[[0,168],[168]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
