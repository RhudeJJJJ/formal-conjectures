/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode037
import Proofs.RadenkovicGutmanD27Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-25],[0]],[[0,0],[0]],[[-375,0],[0,0]],[[0,0],[0,0]],[[-2350,0],[0,0]],[[0,0],[0,0]],[[-7975,0],[0,0]],[[0,0],[0,0]],[[-15900,0],[0,0]],[[0,0],[0,0]],[[-18900,-25],[-25,0]],[[0,0],[0,0]],[[-12850,-200],[-200,0]],[[0,0],[0,0]],[[-4175,-550],[-550,0]],[[0,0],[0,0]],[[-75,-600],[-600,0]],[[0,0],[0,0]],[[225,-225],[-225,0]],[[0],[0,0]],[[0],[0,-25]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
