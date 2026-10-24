/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode201
import Proofs.RadenkovicGutmanD4Long00CompositionalNode203
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .plus e201 e203
noncomputable def p204 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[46,0],[0,0]],[[0,0],[0,0]],[[440,0],[0,0]],[[0,0],[0,0]],[[2306,0],[0,0]],[[0,0],[0,0]],[[7300,0],[0,0]],[[0,0],[0,0]],[[14456,2],[2,0]],[[0,0],[0,0]],[[17884,28],[28,0]],[[0,0],[0,0]],[[13346,132],[132,0]],[[0,0],[0,0]],[[5506,264],[264,0]],[[0,0],[0,0]],[[1014,218],[218,0]],[[0,0],[0,0]],[[36,60],[60,2]],[[0],[0,0]],[[0],[0,4]]]
theorem step204 : p204=NestedHorner.add p201 p203 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_plus e204 e201 e203 p201 p203 p204 rfl h201 h203 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
