/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode204
import Proofs.RadenkovicGutmanD11Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[22,0],[0]],[[0,0],[0]],[[352,0],[0]],[[0,0],[0]],[[2354,0],[0]],[[0,0],[0]],[[8536,0],[0]],[[0,0],[0]],[[18216,0],[0]],[[0,0],[0]],[[23232,22],[22]],[[0,0],[0]],[[17138,154],[154]],[[0,0],[0]],[[6600,352],[352]],[[0,0],[0]],[[990,286],[286]],[[0,0],[0]],[[0,66],[66]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
