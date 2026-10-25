/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode030
import Proofs.RadenkovicGutmanD22Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[22],[0]],[[0,0],[0]],[[352,0],[0]],[[0,0],[0]],[[2354,0],[0]],[[0,0],[0]],[[8536,0],[0]],[[0,0],[0]],[[18216,0],[0]],[[0,0],[0]],[[23232,22],[22]],[[0,0],[0]],[[17138,154],[154]],[[0,0],[0]],[[6600,352],[352]],[[0,0],[0]],[[990,286],[286]],[[0,0],[0]],[[0,66],[66]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
