/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode159
import Proofs.RadenkovicGutmanD27Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-25],[0]],[[0,0],[0]],[[-375,0],[0,0]],[[0,0],[0,0]],[[-2350,0],[0,0]],[[0,0],[0,0]],[[-7975,0],[0,0]],[[0,0],[0,0]],[[-15900,0],[0,0]],[[0,0],[0,0]],[[-18900,-25],[-25,0]],[[0,0],[0,0]],[[-12850,-200],[-200,0]],[[0,0],[0,0]],[[-4175,-550],[-550,0]],[[0,0],[0,0]],[[-75,-600],[-600,0]],[[0,0],[0,0]],[[225,-225],[-225,0]],[[0],[0,0]],[[0],[0,-25]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
