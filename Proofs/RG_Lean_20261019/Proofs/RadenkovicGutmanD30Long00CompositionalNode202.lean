/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode191
import Proofs.RadenkovicGutmanD30Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[64,0],[0,0]],[[0,0],[0,0]],[[754,0],[0,0]],[[0,0],[0,0]],[[4622,0],[0,0]],[[0,0],[0,0]],[[16702,0],[0,0]],[[0,0],[0,0]],[[37368,2],[2,0]],[[0,0],[0,0]],[[52180,46],[46,0]],[[0,0],[0,0]],[[44294,284],[284,0]],[[0,0],[0,0]],[[21228,708],[708,0]],[[0,0],[0,0]],[[4788,738],[738,0]],[[0,0],[0,0]],[[270,270],[270,2]],[[0],[0,0]],[[0],[0,30]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
