/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode202
import Proofs.RadenkovicGutmanD19Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[53,0],[0,0]],[[0,0],[0,0]],[[567,0],[0,0]],[[0,0],[0,0]],[[3280,0],[0,0]],[[0,0],[0,0]],[[11411,0],[0,0]],[[0,0],[0,0]],[[24872,2],[2,0]],[[0,0],[0,0]],[[34096,35],[35,0]],[[0,0],[0,0]],[[28564,196],[196,0]],[[0,0],[0,0]],[[13561,466],[466,0]],[[0,0],[0,0]],[[3039,474],[474,0]],[[0,0],[0,0]],[[171,171],[171,2]],[[0],[0,0]],[[0],[0,19]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
