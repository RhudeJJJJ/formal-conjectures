/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode030
import Proofs.RadenkovicGutmanD41Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[41],[0]],[[0,0],[0]],[[697,0],[0,0]],[[0,0],[0,0]],[[5002,0],[0,0]],[[0,0],[0,0]],[[19721,0],[0,0]],[[0,0],[0,0]],[[46576,0],[0,0]],[[0,0],[0,0]],[[67404,41],[41,0]],[[0,0],[0,0]],[[58630,328],[328,0]],[[0,0],[0,0]],[[28577,902],[902,0]],[[0,0],[0,0]],[[6519,984],[984,0]],[[0,0],[0,0]],[[369,369],[369,0]],[[0],[0,0]],[[0],[0,41]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
