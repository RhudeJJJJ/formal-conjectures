/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode037
import Proofs.RadenkovicGutmanD27Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-25]],[[0,0],[0]],[[225,-225],[-225]],[[0,0],[0]],[[-75,-600],[-600]],[[0,0],[0]],[[-4175,-550],[-550]],[[0,0],[0]],[[-12850,-200],[-200]],[[0,0],[0]],[[-18900,-25],[-25]],[[0]],[[-15900]],[[0]],[[-7975]],[[0]],[[-2350]],[[0]],[[-375]],[[0]],[[-25]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
