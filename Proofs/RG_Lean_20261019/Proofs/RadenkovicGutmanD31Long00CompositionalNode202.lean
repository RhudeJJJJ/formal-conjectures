/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode191
import Proofs.RadenkovicGutmanD31Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[65,0],[0,0]],[[0,0],[0,0]],[[771,0],[0,0]],[[0,0],[0,0]],[[4744,0],[0,0]],[[0,0],[0,0]],[[17183,0],[0,0]],[[0,0],[0,0]],[[38504,2],[2,0]],[[0,0],[0,0]],[[53824,47],[47,0]],[[0,0],[0,0]],[[45724,292],[292,0]],[[0,0],[0,0]],[[21925,730],[730,0]],[[0,0],[0,0]],[[4947,762],[762,0]],[[0,0],[0,0]],[[279,279],[279,2]],[[0],[0,0]],[[0],[0,31]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
