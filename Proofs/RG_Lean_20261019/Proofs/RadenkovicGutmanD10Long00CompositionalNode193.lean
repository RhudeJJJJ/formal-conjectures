/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode192
import Proofs.RadenkovicGutmanD10Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[40,0],[0,0]],[[0,0],[0,0]],[[338,0],[0,0]],[[0,0],[0,0]],[[1578,0],[0,0]],[[0,0],[0,0]],[[4462,0],[0,0]],[[0,0],[0,0]],[[7872,2],[2,0]],[[0,0],[0,0]],[[8588,26],[26,0]],[[0,0],[0,0]],[[5474,124],[124,0]],[[0,0],[0,0]],[[1676,268],[268,0]],[[0,0],[0,0]],[[12,258],[258,0]],[[0,0],[0,0]],[[-90,90],[90,2]],[[0],[0,0]],[[0],[0,10]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
