/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode176
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e176 e121
noncomputable def p177 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-68,0],[0,0]],[[0,0],[0,0]],[[-488,0],[0,0]],[[0,0],[0,0]],[[-1924,0],[0,0]],[[0,0],[0,0]],[[-4544,0],[0,0]],[[0,0],[0,0]],[[-6576,-4],[-4,0]],[[0,0],[0,0]],[[-5720,-32],[-32,0]],[[0,0],[0,0]],[[-2788,-88],[-88,0]],[[0,0],[0,0]],[[-636,-96],[-96,0]],[[0,0],[0,0]],[[-36,-36],[-36,0]],[[0],[0,0]],[[0],[0,-4]]]
theorem step177 : p177=NestedArithmetic.mul p176 p121 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e176 e121 p176 p121 p177 rfl h176 h121 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
