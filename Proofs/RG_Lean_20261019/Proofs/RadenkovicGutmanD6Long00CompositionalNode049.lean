/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode045
import Proofs.RadenkovicGutmanD6Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,6]],[[0,0],[0,0]],[[-54,90],[90,2]],[[0,0],[0]],[[648,318],[318]],[[0,0],[0]],[[5544,372],[372]],[[0,0],[0]],[[15946,176],[176]],[[0,0],[0]],[[23732,34],[34]],[[0,0],[0]],[[20592,2],[2]],[[0]],[[10842]],[[0]],[[3458]],[[0]],[[638]],[[0]],[[60]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
