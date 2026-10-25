/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode044
import Proofs.RadenkovicGutmanD30Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,30]],[[0,0],[0,0]],[[270,270],[270,2]],[[0,0],[0]],[[4788,738],[738]],[[0,0],[0]],[[21228,708],[708]],[[0,0],[0]],[[44294,284],[284]],[[0,0],[0]],[[52180,46],[46]],[[0,0],[0]],[[37368,2],[2]],[[0]],[[16702]],[[0]],[[4622]],[[0]],[[754]],[[0]],[[64]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
