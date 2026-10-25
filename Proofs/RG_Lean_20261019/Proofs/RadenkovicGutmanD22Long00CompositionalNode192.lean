/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode191
import Proofs.RadenkovicGutmanD22Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[52,0],[0,0]],[[0,0],[0,0]],[[518,0],[0,0]],[[0,0],[0,0]],[[2706,0],[0,0]],[[0,0],[0,0]],[[8290,0],[0,0]],[[0,0],[0,0]],[[15504,2],[2,0]],[[0,0],[0,0]],[[17660,38],[38,0]],[[0,0],[0,0]],[[11642,220],[220,0]],[[0,0],[0,0]],[[3680,532],[532,0]],[[0,0],[0,0]],[[48,546],[546,0]],[[0,0],[0,0]],[[-198,198],[198,2]],[[0],[0,0]],[[0],[0,22]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
