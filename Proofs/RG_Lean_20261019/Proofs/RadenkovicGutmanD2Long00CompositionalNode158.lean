/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode157
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e158 : NestedArithmetic.Expr 3 := .times e157 e120
noncomputable def p158 : NestedHorner.Poly 3 := [[[0],[0]],[[0,0],[0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0,0],[0,0]],[[0],[0,0]],[[0],[0,0]]]
theorem step158 : p158=NestedArithmetic.mul p157 p120 := by decide +kernel
#print axioms step158
theorem h158 : NestedArithmetic.compile e158=p158 := StagedExprCompile.compile_times e158 e157 e120 p157 p120 p158 rfl h157 h120 step158
#print axioms h158
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
