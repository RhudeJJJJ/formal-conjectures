/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode045
import Proofs.RadenkovicGutmanD29Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,29]],[[0,0],[0,0]],[[-261,435],[435,2]],[[0,0],[0]],[[3201,1468],[1468]],[[0,0],[0]],[[26773,1614],[1614]],[[0,0],[0]],[[75792,682],[682]],[[0,0],[0]],[[110764,103],[103]],[[0,0],[0]],[[93732,2],[2]],[[0]],[[47527]],[[0]],[[14268]],[[0]],[[2363]],[[0]],[[175]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
