/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode044
import Proofs.RadenkovicGutmanD19Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,19]],[[0,0],[0,0]],[[171,171],[171,2]],[[0,0],[0]],[[3039,474],[474]],[[0,0],[0]],[[13561,466],[466]],[[0,0],[0]],[[28564,196],[196]],[[0,0],[0]],[[34096,35],[35]],[[0,0],[0]],[[24872,2],[2]],[[0]],[[11411]],[[0]],[[3280]],[[0]],[[567]],[[0]],[[53]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
