/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode045
import Proofs.RadenkovicGutmanD45Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,45]],[[0,0],[0,0]],[[-405,675],[675,2]],[[0,0],[0]],[[4977,2268],[2268]],[[0,0],[0]],[[41541,2478],[2478]],[[0,0],[0]],[[117424,1034],[1034]],[[0,0],[0]],[[171308,151],[151]],[[0,0],[0]],[[144612,2],[2]],[[0]],[[73047]],[[0]],[[21788]],[[0]],[[3563]],[[0]],[[255]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
