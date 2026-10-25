/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode037
import Proofs.RadenkovicGutmanD24Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-330,0],[0,0]],[[0,0],[0,0]],[[-2068,0],[0,0]],[[0,0],[0,0]],[[-7018,0],[0,0]],[[0,0],[0,0]],[[-13992,0],[0,0]],[[0,0],[0,0]],[[-16632,-22],[-22,0]],[[0,0],[0,0]],[[-11308,-176],[-176,0]],[[0,0],[0,0]],[[-3674,-484],[-484,0]],[[0,0],[0,0]],[[-66,-528],[-528,0]],[[0,0],[0,0]],[[198,-198],[-198,0]],[[0],[0,0]],[[0],[0,-22]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
