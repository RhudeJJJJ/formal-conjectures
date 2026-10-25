/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode159
import Proofs.RadenkovicGutmanD15Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-13],[0]],[[0,0],[0]],[[-195,0],[0,0]],[[0,0],[0,0]],[[-1222,0],[0,0]],[[0,0],[0,0]],[[-4147,0],[0,0]],[[0,0],[0,0]],[[-8268,0],[0,0]],[[0,0],[0,0]],[[-9828,-13],[-13,0]],[[0,0],[0,0]],[[-6682,-104],[-104,0]],[[0,0],[0,0]],[[-2171,-286],[-286,0]],[[0,0],[0,0]],[[-39,-312],[-312,0]],[[0,0],[0,0]],[[117,-117],[-117,0]],[[0],[0,0]],[[0],[0,-13]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
