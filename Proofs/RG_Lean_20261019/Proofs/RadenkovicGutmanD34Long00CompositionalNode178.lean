/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode177
import Proofs.RadenkovicGutmanD34Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-64],[0]],[[0,0],[0]],[[-1088,0],[0,0]],[[0,0],[0,0]],[[-7808,0],[0,0]],[[0,0],[0,0]],[[-30784,0],[0,0]],[[0,0],[0,0]],[[-72704,0],[0,0]],[[0,0],[0,0]],[[-105216,-64],[-64,0]],[[0,0],[0,0]],[[-91520,-512],[-512,0]],[[0,0],[0,0]],[[-44608,-1408],[-1408,0]],[[0,0],[0,0]],[[-10176,-1536],[-1536,0]],[[0,0],[0,0]],[[-576,-576],[-576,0]],[[0],[0,0]],[[0],[0,-64]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
