/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode030
import Proofs.RadenkovicGutmanD19Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[19],[0]],[[0,0],[0]],[[285,0],[0,0]],[[0,0],[0,0]],[[1786,0],[0,0]],[[0,0],[0,0]],[[6061,0],[0,0]],[[0,0],[0,0]],[[12084,0],[0,0]],[[0,0],[0,0]],[[14364,19],[19,0]],[[0,0],[0,0]],[[9766,152],[152,0]],[[0,0],[0,0]],[[3173,418],[418,0]],[[0,0],[0,0]],[[57,456],[456,0]],[[0,0],[0,0]],[[-171,171],[171,0]],[[0],[0,0]],[[0],[0,19]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
