/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode030
import Proofs.RadenkovicGutmanD23Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[23],[0]],[[0,0],[0]],[[391,0],[0,0]],[[0,0],[0,0]],[[2806,0],[0,0]],[[0,0],[0,0]],[[11063,0],[0,0]],[[0,0],[0,0]],[[26128,0],[0,0]],[[0,0],[0,0]],[[37812,23],[23,0]],[[0,0],[0,0]],[[32890,184],[184,0]],[[0,0],[0,0]],[[16031,506],[506,0]],[[0,0],[0,0]],[[3657,552],[552,0]],[[0,0],[0,0]],[[207,207],[207,0]],[[0],[0,0]],[[0],[0,23]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
