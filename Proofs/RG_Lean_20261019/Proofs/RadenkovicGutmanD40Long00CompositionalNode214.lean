/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode030
import Proofs.RadenkovicGutmanD40Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[40],[0]],[[0,0],[0]],[[680,0],[0,0]],[[0,0],[0,0]],[[4880,0],[0,0]],[[0,0],[0,0]],[[19240,0],[0,0]],[[0,0],[0,0]],[[45440,0],[0,0]],[[0,0],[0,0]],[[65760,40],[40,0]],[[0,0],[0,0]],[[57200,320],[320,0]],[[0,0],[0,0]],[[27880,880],[880,0]],[[0,0],[0,0]],[[6360,960],[960,0]],[[0,0],[0,0]],[[360,360],[360,0]],[[0],[0,0]],[[0],[0,40]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
