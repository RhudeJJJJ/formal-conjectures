/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode174
import Proofs.RadenkovicGutmanD34Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-64],[0]],[[0,0],[0]],[[-1088,0],[0,0]],[[0,0],[0,0]],[[-7808,0],[0,0]],[[0,0],[0,0]],[[-30784,0],[0,0]],[[0,0],[0,0]],[[-72704,0],[0,0]],[[0,0],[0,0]],[[-105216,-64],[-64,0]],[[0,0],[0,0]],[[-91520,-512],[-512,0]],[[0,0],[0,0]],[[-44608,-1408],[-1408,0]],[[0,0],[0,0]],[[-10176,-1536],[-1536,0]],[[0,0],[0,0]],[[-576,-576],[-576,0]],[[0],[0,0]],[[0],[0,-64]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
