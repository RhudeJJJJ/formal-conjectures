/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode177
import Proofs.RadenkovicGutmanD16Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-476,0],[0,0]],[[0,0],[0,0]],[[-3416,0],[0,0]],[[0,0],[0,0]],[[-13468,0],[0,0]],[[0,0],[0,0]],[[-31808,0],[0,0]],[[0,0],[0,0]],[[-46032,-28],[-28,0]],[[0,0],[0,0]],[[-40040,-224],[-224,0]],[[0,0],[0,0]],[[-19516,-616],[-616,0]],[[0,0],[0,0]],[[-4452,-672],[-672,0]],[[0,0],[0,0]],[[-252,-252],[-252,0]],[[0],[0,0]],[[0],[0,-28]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
