/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode191
import Proofs.RadenkovicGutmanD39Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[69,0],[0,0]],[[0,0],[0,0]],[[773,0],[0,0]],[[0,0],[0,0]],[[4304,0],[0,0]],[[0,0],[0,0]],[[13713,0],[0,0]],[[0,0],[0,0]],[[26316,2],[2,0]],[[0,0],[0,0]],[[30512,55],[55,0]],[[0,0],[0,0]],[[20380,356],[356,0]],[[0,0],[0,0]],[[6519,906],[906,0]],[[0,0],[0,0]],[[99,954],[954,0]],[[0,0],[0,0]],[[-351,351],[351,2]],[[0],[0,0]],[[0],[0,39]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
