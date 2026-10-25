/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode191
import Proofs.RadenkovicGutmanD41Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[75,0],[0,0]],[[0,0],[0,0]],[[941,0],[0,0]],[[0,0],[0,0]],[[5964,0],[0,0]],[[0,0],[0,0]],[[21993,0],[0,0]],[[0,0],[0,0]],[[49864,2],[2,0]],[[0,0],[0,0]],[[70264,57],[57,0]],[[0,0],[0,0]],[[60024,372],[372,0]],[[0,0],[0,0]],[[28895,950],[950,0]],[[0,0],[0,0]],[[6537,1002],[1002,0]],[[0,0],[0,0]],[[369,369],[369,2]],[[0],[0,0]],[[0],[0,41]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
