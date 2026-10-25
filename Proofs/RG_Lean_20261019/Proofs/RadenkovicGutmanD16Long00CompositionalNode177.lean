/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode174
import Proofs.RadenkovicGutmanD16Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-476,0],[0,0]],[[0,0],[0,0]],[[-3416,0],[0,0]],[[0,0],[0,0]],[[-13468,0],[0,0]],[[0,0],[0,0]],[[-31808,0],[0,0]],[[0,0],[0,0]],[[-46032,-28],[-28,0]],[[0,0],[0,0]],[[-40040,-224],[-224,0]],[[0,0],[0,0]],[[-19516,-616],[-616,0]],[[0,0],[0,0]],[[-4452,-672],[-672,0]],[[0,0],[0,0]],[[-252,-252],[-252,0]],[[0],[0,0]],[[0],[0,-28]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
