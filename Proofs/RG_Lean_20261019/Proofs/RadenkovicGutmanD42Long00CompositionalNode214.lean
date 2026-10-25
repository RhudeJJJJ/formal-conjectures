/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode030
import Proofs.RadenkovicGutmanD42Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[42],[0]],[[0,0],[0]],[[714,0],[0,0]],[[0,0],[0,0]],[[5124,0],[0,0]],[[0,0],[0,0]],[[20202,0],[0,0]],[[0,0],[0,0]],[[47712,0],[0,0]],[[0,0],[0,0]],[[69048,42],[42,0]],[[0,0],[0,0]],[[60060,336],[336,0]],[[0,0],[0,0]],[[29274,924],[924,0]],[[0,0],[0,0]],[[6678,1008],[1008,0]],[[0,0],[0,0]],[[378,378],[378,0]],[[0],[0,0]],[[0],[0,42]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
