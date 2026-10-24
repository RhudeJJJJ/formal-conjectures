/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode035
import Proofs.RadenkovicGutmanD4Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .times e035 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-4]],[[0,0],[0]],[[108,-36],[-36]],[[0,0],[0]],[[612,-96],[-96]],[[0,0],[0]],[[1452,-88],[-88]],[[0,0],[0]],[[1608,-32],[-32]],[[0,0],[0]],[[528,-4],[-4]],[[0]],[[-544]],[[0]],[[-628]],[[0]],[[-264]],[[0]],[[-52]],[[0]],[[-4]]]
theorem step040 : p040=NestedArithmetic.mul p035 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_times e040 e035 e039 p035 p039 p040 rfl h035 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
