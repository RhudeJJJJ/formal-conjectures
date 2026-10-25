/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode192
import Proofs.RadenkovicGutmanD39Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[69,0],[0,0]],[[0,0],[0,0]],[[773,0],[0,0]],[[0,0],[0,0]],[[4304,0],[0,0]],[[0,0],[0,0]],[[13713,0],[0,0]],[[0,0],[0,0]],[[26316,2],[2,0]],[[0,0],[0,0]],[[30512,55],[55,0]],[[0,0],[0,0]],[[20380,356],[356,0]],[[0,0],[0,0]],[[6519,906],[906,0]],[[0,0],[0,0]],[[99,954],[954,0]],[[0,0],[0,0]],[[-351,351],[351,2]],[[0],[0,0]],[[0],[0,39]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
