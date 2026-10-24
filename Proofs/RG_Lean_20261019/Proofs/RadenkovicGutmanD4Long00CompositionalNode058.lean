/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode057
import Proofs.RadenkovicGutmanD4Long00CompositionalNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e058 : NestedArithmetic.Expr 3 := .times e057 e051
noncomputable def p058 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-4]],[[0,0],[0]],[[-36,-36],[-36]],[[0,0],[0]],[[-636,-96],[-96]],[[0,0],[0]],[[-2788,-88],[-88]],[[0,0],[0]],[[-5720,-32],[-32]],[[0,0],[0]],[[-6576,-4],[-4]],[[0]],[[-4544]],[[0]],[[-1924]],[[0]],[[-488]],[[0]],[[-68]],[[0]],[[-4]]]
theorem step058 : p058=NestedArithmetic.mul p057 p051 := by decide +kernel
#print axioms step058
theorem h058 : NestedArithmetic.compile e058=p058 := StagedExprCompile.compile_times e058 e057 e051 p057 p051 p058 rfl h057 h051 step058
#print axioms h058
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
