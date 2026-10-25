/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode045
import Proofs.RadenkovicGutmanD31Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,31]],[[0,0],[0,0]],[[-279,465],[465,2]],[[0,0],[0]],[[3423,1568],[1568]],[[0,0],[0]],[[28619,1722],[1722]],[[0,0],[0]],[[80996,726],[726]],[[0,0],[0]],[[118332,109],[109]],[[0,0],[0]],[[100092,2],[2]],[[0]],[[50717]],[[0]],[[15208]],[[0]],[[2513]],[[0]],[[185]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
