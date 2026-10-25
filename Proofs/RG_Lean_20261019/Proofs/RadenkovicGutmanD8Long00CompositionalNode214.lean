/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode030
import Proofs.RadenkovicGutmanD8Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[8],[0]],[[0,0],[0]],[[136,0],[0,0]],[[0,0],[0,0]],[[976,0],[0,0]],[[0,0],[0,0]],[[3848,0],[0,0]],[[0,0],[0,0]],[[9088,0],[0,0]],[[0,0],[0,0]],[[13152,8],[8,0]],[[0,0],[0,0]],[[11440,64],[64,0]],[[0,0],[0,0]],[[5576,176],[176,0]],[[0,0],[0,0]],[[1272,192],[192,0]],[[0,0],[0,0]],[[72,72],[72,0]],[[0],[0,0]],[[0],[0,8]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
