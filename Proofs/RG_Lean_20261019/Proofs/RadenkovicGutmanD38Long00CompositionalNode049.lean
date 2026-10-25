/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode045
import Proofs.RadenkovicGutmanD38Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,38]],[[0,0],[0,0]],[[-342,570],[570,2]],[[0,0],[0]],[[4200,1918],[1918]],[[0,0],[0]],[[35080,2100],[2100]],[[0,0],[0]],[[99210,880],[880]],[[0,0],[0]],[[144820,130],[130]],[[0,0],[0]],[[122352,2],[2]],[[0]],[[61882]],[[0]],[[18498]],[[0]],[[3038]],[[0]],[[220]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
