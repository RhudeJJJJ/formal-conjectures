/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode060
import Proofs.RadenkovicGutmanD2Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .plus e060 e061
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,2]],[[0,0],[0,0]],[[18,30],[30,2]],[[0,0],[0]],[[516,118],[118]],[[0,0],[0]],[[2912,156],[156]],[[0,0],[0]],[[7370,88],[88]],[[0,0],[0]],[[10372,22],[22]],[[0,0],[0]],[[8872,2],[2]],[[0]],[[4786]],[[0]],[[1634]],[[0]],[[342]],[[0]],[[40]],[[0]],[[2]]]
theorem step062 : p062=NestedHorner.add p060 p061 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_plus e062 e060 e061 p060 p061 p062 rfl h060 h061 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
