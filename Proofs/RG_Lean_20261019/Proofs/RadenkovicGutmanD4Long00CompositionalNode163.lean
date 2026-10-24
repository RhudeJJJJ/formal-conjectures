/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode118
import Proofs.RadenkovicGutmanD4Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .times e118 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-52,0],[0,0]],[[0,0],[0,0]],[[-264,0],[0,0]],[[0,0],[0,0]],[[-628,0],[0,0]],[[0,0],[0,0]],[[-544,0],[0,0]],[[0,0],[0,0]],[[528,-4],[-4,0]],[[0,0],[0,0]],[[1608,-32],[-32,0]],[[0,0],[0,0]],[[1452,-88],[-88,0]],[[0,0],[0,0]],[[612,-96],[-96,0]],[[0,0],[0,0]],[[108,-36],[-36,0]],[[0],[0,0]],[[0],[0,-4]]]
theorem step163 : p163=NestedArithmetic.mul p118 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_times e163 e118 e162 p118 p162 p163 rfl h118 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
