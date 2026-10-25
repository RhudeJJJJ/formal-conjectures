/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode202
import Proofs.RadenkovicGutmanD30Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[64,0],[0,0]],[[0,0],[0,0]],[[754,0],[0,0]],[[0,0],[0,0]],[[4622,0],[0,0]],[[0,0],[0,0]],[[16702,0],[0,0]],[[0,0],[0,0]],[[37368,2],[2,0]],[[0,0],[0,0]],[[52180,46],[46,0]],[[0,0],[0,0]],[[44294,284],[284,0]],[[0,0],[0,0]],[[21228,708],[708,0]],[[0,0],[0,0]],[[4788,738],[738,0]],[[0,0],[0,0]],[[270,270],[270,2]],[[0],[0,0]],[[0],[0,30]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
