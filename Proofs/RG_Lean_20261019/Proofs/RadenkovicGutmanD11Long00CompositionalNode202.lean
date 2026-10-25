/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode191
import Proofs.RadenkovicGutmanD11Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[45,0],[0,0]],[[0,0],[0,0]],[[431,0],[0,0]],[[0,0],[0,0]],[[2304,0],[0,0]],[[0,0],[0,0]],[[7563,0],[0,0]],[[0,0],[0,0]],[[15784,2],[2,0]],[[0,0],[0,0]],[[20944,27],[27,0]],[[0,0],[0,0]],[[17124,132],[132,0]],[[0,0],[0,0]],[[7985,290],[290,0]],[[0,0],[0,0]],[[1767,282],[282,0]],[[0,0],[0,0]],[[99,99],[99,2]],[[0],[0,0]],[[0],[0,11]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
