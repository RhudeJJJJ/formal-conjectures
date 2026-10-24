/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode175
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e212 : NestedArithmetic.Expr 3 := .times e009 e175
noncomputable def p212 : NestedHorner.Poly 3 := [[[4],[0]],[[0,0],[0]],[[68,0],[0,0]],[[0,0],[0,0]],[[488,0],[0,0]],[[0,0],[0,0]],[[1924,0],[0,0]],[[0,0],[0,0]],[[4544,0],[0,0]],[[0,0],[0,0]],[[6576,4],[4,0]],[[0,0],[0,0]],[[5720,32],[32,0]],[[0,0],[0,0]],[[2788,88],[88,0]],[[0,0],[0,0]],[[636,96],[96,0]],[[0,0],[0,0]],[[36,36],[36,0]],[[0],[0,0]],[[0],[0,4]]]
theorem step212 : p212=NestedArithmetic.mul p009 p175 := by decide +kernel
#print axioms step212
theorem h212 : NestedArithmetic.compile e212=p212 := StagedExprCompile.compile_times e212 e009 e175 p009 p175 p212 rfl h009 h175 step212
#print axioms h212
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
