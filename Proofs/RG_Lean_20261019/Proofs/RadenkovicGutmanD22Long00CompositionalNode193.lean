/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode192
import Proofs.RadenkovicGutmanD22Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[52,0],[0,0]],[[0,0],[0,0]],[[518,0],[0,0]],[[0,0],[0,0]],[[2706,0],[0,0]],[[0,0],[0,0]],[[8290,0],[0,0]],[[0,0],[0,0]],[[15504,2],[2,0]],[[0,0],[0,0]],[[17660,38],[38,0]],[[0,0],[0,0]],[[11642,220],[220,0]],[[0,0],[0,0]],[[3680,532],[532,0]],[[0,0],[0,0]],[[48,546],[546,0]],[[0,0],[0,0]],[[-198,198],[198,2]],[[0],[0,0]],[[0],[0,22]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
