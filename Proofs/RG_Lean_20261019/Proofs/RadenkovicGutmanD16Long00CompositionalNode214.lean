/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode030
import Proofs.RadenkovicGutmanD16Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[16],[0]],[[0,0],[0]],[[272,0],[0,0]],[[0,0],[0,0]],[[1952,0],[0,0]],[[0,0],[0,0]],[[7696,0],[0,0]],[[0,0],[0,0]],[[18176,0],[0,0]],[[0,0],[0,0]],[[26304,16],[16,0]],[[0,0],[0,0]],[[22880,128],[128,0]],[[0,0],[0,0]],[[11152,352],[352,0]],[[0,0],[0,0]],[[2544,384],[384,0]],[[0,0],[0,0]],[[144,144],[144,0]],[[0],[0,0]],[[0],[0,16]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
