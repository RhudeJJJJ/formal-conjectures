/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode191
import Proofs.RadenkovicGutmanD19Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[53,0],[0,0]],[[0,0],[0,0]],[[567,0],[0,0]],[[0,0],[0,0]],[[3280,0],[0,0]],[[0,0],[0,0]],[[11411,0],[0,0]],[[0,0],[0,0]],[[24872,2],[2,0]],[[0,0],[0,0]],[[34096,35],[35,0]],[[0,0],[0,0]],[[28564,196],[196,0]],[[0,0],[0,0]],[[13561,466],[466,0]],[[0,0],[0,0]],[[3039,474],[474,0]],[[0,0],[0,0]],[[171,171],[171,2]],[[0],[0,0]],[[0],[0,19]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
