/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode200
import Proofs.RadenkovicGutmanD2Long00CompositionalNode202
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .plus e200 e202
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[40,0],[0,0]],[[0,0],[0,0]],[[342,0],[0,0]],[[0,0],[0,0]],[[1634,0],[0,0]],[[0,0],[0,0]],[[4786,0],[0,0]],[[0,0],[0,0]],[[8872,2],[2,0]],[[0,0],[0,0]],[[10372,22],[22,0]],[[0,0],[0,0]],[[7370,88],[88,0]],[[0,0],[0,0]],[[2912,156],[156,0]],[[0,0],[0,0]],[[516,118],[118,0]],[[0,0],[0,0]],[[18,30],[30,2]],[[0],[0,0]],[[0],[0,2]]]
theorem step203 : p203=NestedHorner.add p200 p202 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_plus e203 e200 e202 p200 p202 p203 rfl h200 h202 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
