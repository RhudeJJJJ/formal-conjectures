/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode192
import Proofs.RadenkovicGutmanD32Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[62,0],[0,0]],[[0,0],[0,0]],[[668,0],[0,0]],[[0,0],[0,0]],[[3646,0],[0,0]],[[0,0],[0,0]],[[11480,0],[0,0]],[[0,0],[0,0]],[[21864,2],[2,0]],[[0,0],[0,0]],[[25220,48],[48,0]],[[0,0],[0,0]],[[16782,300],[300,0]],[[0,0],[0,0]],[[5350,752],[752,0]],[[0,0],[0,0]],[[78,786],[786,0]],[[0,0],[0,0]],[[-288,288],[288,2]],[[0],[0,0]],[[0],[0,32]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
