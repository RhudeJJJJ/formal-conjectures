/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode163
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e163 e121
noncomputable def p164 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-52,0],[0,0]],[[0,0],[0,0]],[[-264,0],[0,0]],[[0,0],[0,0]],[[-628,0],[0,0]],[[0,0],[0,0]],[[-544,0],[0,0]],[[0,0],[0,0]],[[528,-4],[-4,0]],[[0,0],[0,0]],[[1608,-32],[-32,0]],[[0,0],[0,0]],[[1452,-88],[-88,0]],[[0,0],[0,0]],[[612,-96],[-96,0]],[[0,0],[0,0]],[[108,-36],[-36,0]],[[0],[0,0]],[[0],[0,-4]]]
theorem step164 : p164=NestedArithmetic.mul p163 p121 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e163 e121 p163 p121 p164 rfl h163 h121 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
