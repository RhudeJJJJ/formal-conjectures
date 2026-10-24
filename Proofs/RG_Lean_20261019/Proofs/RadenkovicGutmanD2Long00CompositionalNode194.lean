/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode190
import Proofs.RadenkovicGutmanD2Long00CompositionalNode193
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e194 : NestedArithmetic.Expr 3 := .plus e190 e193
noncomputable def p194 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[40,0],[0,0]],[[0,0],[0,0]],[[338,0],[0,0]],[[0,0],[0,0]],[[1578,0],[0,0]],[[0,0],[0,0]],[[4462,0],[0,0]],[[0,0],[0,0]],[[7872,2],[2,0]],[[0,0],[0,0]],[[8596,22],[22,0]],[[0,0],[0,0]],[[5538,88],[88,0]],[[0,0],[0,0]],[[1852,156],[156,0]],[[0,0],[0,0]],[[204,118],[118,0]],[[0,0],[0,0]],[[-18,30],[30,2]],[[0],[0,0]],[[0],[0,2]]]
theorem step194 : p194=NestedHorner.add p190 p193 := by decide +kernel
#print axioms step194
theorem h194 : NestedArithmetic.compile e194=p194 := StagedExprCompile.compile_plus e194 e190 e193 p190 p193 p194 rfl h190 h193 step194
#print axioms h194
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
