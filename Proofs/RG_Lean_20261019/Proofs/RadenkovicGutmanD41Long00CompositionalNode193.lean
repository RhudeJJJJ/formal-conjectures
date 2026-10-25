/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode192
import Proofs.RadenkovicGutmanD41Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[71,0],[0,0]],[[0,0],[0,0]],[[803,0],[0,0]],[[0,0],[0,0]],[[4492,0],[0,0]],[[0,0],[0,0]],[[14351,0],[0,0]],[[0,0],[0,0]],[[27588,2],[2,0]],[[0,0],[0,0]],[[32024,57],[57,0]],[[0,0],[0,0]],[[21408,372],[372,0]],[[0,0],[0,0]],[[6853,950],[950,0]],[[0,0],[0,0]],[[105,1002],[1002,0]],[[0,0],[0,0]],[[-369,369],[369,2]],[[0],[0,0]],[[0],[0,41]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
