/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode159
import Proofs.RadenkovicGutmanD24Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-330,0],[0,0]],[[0,0],[0,0]],[[-2068,0],[0,0]],[[0,0],[0,0]],[[-7018,0],[0,0]],[[0,0],[0,0]],[[-13992,0],[0,0]],[[0,0],[0,0]],[[-16632,-22],[-22,0]],[[0,0],[0,0]],[[-11308,-176],[-176,0]],[[0,0],[0,0]],[[-3674,-484],[-484,0]],[[0,0],[0,0]],[[-66,-528],[-528,0]],[[0,0],[0,0]],[[198,-198],[-198,0]],[[0],[0,0]],[[0],[0,-22]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
