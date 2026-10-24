/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode045
import Proofs.RadenkovicGutmanD5Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,5]],[[0,0],[0,0]],[[-45,75],[75,2]],[[0,0],[0]],[[537,268],[268]],[[0,0],[0]],[[4621,318],[318]],[[0,0],[0]],[[13344,154],[154]],[[0,0],[0]],[[19948,31],[31]],[[0,0],[0]],[[17412,2],[2]],[[0]],[[9247]],[[0]],[[2988]],[[0]],[[563]],[[0]],[[55]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
