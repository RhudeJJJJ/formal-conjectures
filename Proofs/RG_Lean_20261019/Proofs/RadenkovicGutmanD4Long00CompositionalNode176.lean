/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode173
import Proofs.RadenkovicGutmanD4Long00CompositionalNode175
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e176 : NestedArithmetic.Expr 3 := .times e173 e175
noncomputable def p176 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-68,0],[0,0]],[[0,0],[0,0]],[[-488,0],[0,0]],[[0,0],[0,0]],[[-1924,0],[0,0]],[[0,0],[0,0]],[[-4544,0],[0,0]],[[0,0],[0,0]],[[-6576,-4],[-4,0]],[[0,0],[0,0]],[[-5720,-32],[-32,0]],[[0,0],[0,0]],[[-2788,-88],[-88,0]],[[0,0],[0,0]],[[-636,-96],[-96,0]],[[0,0],[0,0]],[[-36,-36],[-36,0]],[[0],[0,0]],[[0],[0,-4]]]
theorem step176 : p176=NestedArithmetic.mul p173 p175 := by decide +kernel
#print axioms step176
theorem h176 : NestedArithmetic.compile e176=p176 := StagedExprCompile.compile_times e176 e173 e175 p173 p175 p176 rfl h173 h175 step176
#print axioms h176
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
