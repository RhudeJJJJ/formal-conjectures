/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode044
import Proofs.RadenkovicGutmanD31Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,31]],[[0,0],[0,0]],[[279,279],[279,2]],[[0,0],[0]],[[4947,762],[762]],[[0,0],[0]],[[21925,730],[730]],[[0,0],[0]],[[45724,292],[292]],[[0,0],[0]],[[53824,47],[47]],[[0,0],[0]],[[38504,2],[2]],[[0]],[[17183]],[[0]],[[4744]],[[0]],[[771]],[[0]],[[65]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
