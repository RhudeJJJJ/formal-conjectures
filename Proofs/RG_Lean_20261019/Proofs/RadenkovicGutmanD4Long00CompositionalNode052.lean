/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e052 : NestedArithmetic.Expr 3 := .times e009 e051
noncomputable def p052 : NestedHorner.Poly 3 := [[[0],[0,4]],[[0,0],[0]],[[36,36],[36]],[[0,0],[0]],[[636,96],[96]],[[0,0],[0]],[[2788,88],[88]],[[0,0],[0]],[[5720,32],[32]],[[0,0],[0]],[[6576,4],[4]],[[0]],[[4544]],[[0]],[[1924]],[[0]],[[488]],[[0]],[[68]],[[0]],[[4]]]
theorem step052 : p052=NestedArithmetic.mul p009 p051 := by decide +kernel
#print axioms step052
theorem h052 : NestedArithmetic.compile e052=p052 := StagedExprCompile.compile_times e052 e009 e051 p009 p051 p052 rfl h009 h051 step052
#print axioms h052
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
