/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode061
import Proofs.RadenkovicGutmanD4Long00CompositionalNode062
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e063 : NestedArithmetic.Expr 3 := .plus e061 e062
noncomputable def p063 : NestedHorner.Poly 3 := [[[0],[0,4]],[[0,0],[0,0]],[[36,60],[60,2]],[[0,0],[0]],[[1014,218],[218]],[[0,0],[0]],[[5506,264],[264]],[[0,0],[0]],[[13346,132],[132]],[[0,0],[0]],[[17884,28],[28]],[[0,0],[0]],[[14456,2],[2]],[[0]],[[7300]],[[0]],[[2306]],[[0]],[[440]],[[0]],[[46]],[[0]],[[2]]]
theorem step063 : p063=NestedHorner.add p061 p062 := by decide +kernel
#print axioms step063
theorem h063 : NestedArithmetic.compile e063=p063 := StagedExprCompile.compile_plus e063 e061 e062 p061 p062 p063 rfl h061 h062 step063
#print axioms h063
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
