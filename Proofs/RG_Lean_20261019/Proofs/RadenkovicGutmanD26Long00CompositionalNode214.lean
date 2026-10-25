/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode030
import Proofs.RadenkovicGutmanD26Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[26],[0]],[[0,0],[0]],[[442,0],[0,0]],[[0,0],[0,0]],[[3172,0],[0,0]],[[0,0],[0,0]],[[12506,0],[0,0]],[[0,0],[0,0]],[[29536,0],[0,0]],[[0,0],[0,0]],[[42744,26],[26,0]],[[0,0],[0,0]],[[37180,208],[208,0]],[[0,0],[0,0]],[[18122,572],[572,0]],[[0,0],[0,0]],[[4134,624],[624,0]],[[0,0],[0,0]],[[234,234],[234,0]],[[0],[0,0]],[[0],[0,26]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
