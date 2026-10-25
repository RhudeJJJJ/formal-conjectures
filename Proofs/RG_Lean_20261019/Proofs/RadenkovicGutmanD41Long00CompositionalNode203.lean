/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode202
import Proofs.RadenkovicGutmanD41Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[75,0],[0,0]],[[0,0],[0,0]],[[941,0],[0,0]],[[0,0],[0,0]],[[5964,0],[0,0]],[[0,0],[0,0]],[[21993,0],[0,0]],[[0,0],[0,0]],[[49864,2],[2,0]],[[0,0],[0,0]],[[70264,57],[57,0]],[[0,0],[0,0]],[[60024,372],[372,0]],[[0,0],[0,0]],[[28895,950],[950,0]],[[0,0],[0,0]],[[6537,1002],[1002,0]],[[0,0],[0,0]],[[369,369],[369,2]],[[0],[0,0]],[[0],[0,41]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
