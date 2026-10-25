/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode192
import Proofs.RadenkovicGutmanD12Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[42,0],[0,0]],[[0,0],[0,0]],[[368,0],[0,0]],[[0,0],[0,0]],[[1766,0],[0,0]],[[0,0],[0,0]],[[5100,0],[0,0]],[[0,0],[0,0]],[[9144,2],[2,0]],[[0,0],[0,0]],[[10100,28],[28,0]],[[0,0],[0,0]],[[6502,140],[140,0]],[[0,0],[0,0]],[[2010,312],[312,0]],[[0,0],[0,0]],[[18,306],[306,0]],[[0,0],[0,0]],[[-108,108],[108,2]],[[0],[0,0]],[[0],[0,12]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
