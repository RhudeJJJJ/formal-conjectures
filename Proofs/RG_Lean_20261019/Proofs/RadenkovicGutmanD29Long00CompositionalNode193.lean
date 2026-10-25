/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode192
import Proofs.RadenkovicGutmanD29Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[59,0],[0,0]],[[0,0],[0,0]],[[623,0],[0,0]],[[0,0],[0,0]],[[3364,0],[0,0]],[[0,0],[0,0]],[[10523,0],[0,0]],[[0,0],[0,0]],[[19956,2],[2,0]],[[0,0],[0,0]],[[22952,45],[45,0]],[[0,0],[0,0]],[[15240,276],[276,0]],[[0,0],[0,0]],[[4849,686],[686,0]],[[0,0],[0,0]],[[69,714],[714,0]],[[0,0],[0,0]],[[-261,261],[261,2]],[[0],[0,0]],[[0],[0,29]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
