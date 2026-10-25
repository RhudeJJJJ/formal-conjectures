/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode191
import Proofs.RadenkovicGutmanD18Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[52,0],[0,0]],[[0,0],[0,0]],[[550,0],[0,0]],[[0,0],[0,0]],[[3158,0],[0,0]],[[0,0],[0,0]],[[10930,0],[0,0]],[[0,0],[0,0]],[[23736,2],[2,0]],[[0,0],[0,0]],[[32452,34],[34,0]],[[0,0],[0,0]],[[27134,188],[188,0]],[[0,0],[0,0]],[[12864,444],[444,0]],[[0,0],[0,0]],[[2880,450],[450,0]],[[0,0],[0,0]],[[162,162],[162,2]],[[0],[0,0]],[[0],[0,18]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
