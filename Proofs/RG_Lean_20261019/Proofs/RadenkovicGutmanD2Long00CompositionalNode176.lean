/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode175
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e176 : NestedArithmetic.Expr 3 := .times e175 e120
noncomputable def p176 : NestedHorner.Poly 3 := [[[0],[0]],[[0,0],[0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0],[0,0]],[[0],[0,0]]]
theorem step176 : p176=NestedArithmetic.mul p175 p120 := by decide +kernel
#print axioms step176
theorem h176 : NestedArithmetic.compile e176=p176 := StagedExprCompile.compile_times e176 e175 e120 p175 p120 p176 rfl h175 h120 step176
#print axioms h176
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
