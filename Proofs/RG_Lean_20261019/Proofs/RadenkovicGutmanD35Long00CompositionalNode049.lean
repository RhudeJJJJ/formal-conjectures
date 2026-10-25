/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode045
import Proofs.RadenkovicGutmanD35Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,35]],[[0,0],[0,0]],[[-315,525],[525,2]],[[0,0],[0]],[[3867,1768],[1768]],[[0,0],[0]],[[32311,1938],[1938]],[[0,0],[0]],[[91404,814],[814]],[[0,0],[0]],[[133468,121],[121]],[[0,0],[0]],[[112812,2],[2]],[[0]],[[57097]],[[0]],[[17088]],[[0]],[[2813]],[[0]],[[205]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
