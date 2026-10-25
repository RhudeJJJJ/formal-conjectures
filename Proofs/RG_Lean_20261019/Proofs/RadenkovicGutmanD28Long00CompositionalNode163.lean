/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode160
import Proofs.RadenkovicGutmanD28Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-386,0],[0,0]],[[0,0],[0,0]],[[-2388,0],[0,0]],[[0,0],[0,0]],[[-7970,0],[0,0]],[[0,0],[0,0]],[[-15536,0],[0,0]],[[0,0],[0,0]],[[-17880,-26],[-26,0]],[[0,0],[0,0]],[[-11532,-208],[-208,0]],[[0,0],[0,0]],[[-3282,-572],[-572,0]],[[0,0],[0,0]],[[234,-624],[-624,0]],[[0,0],[0,0]],[[270,-234],[-234,0]],[[0],[0,0]],[[0],[0,-26]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
