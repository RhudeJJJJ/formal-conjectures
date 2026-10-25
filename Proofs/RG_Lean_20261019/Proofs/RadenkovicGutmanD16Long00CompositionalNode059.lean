/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode058
import Proofs.RadenkovicGutmanD16Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-28]],[[0,0],[0]],[[-252,-252],[-252]],[[0,0],[0]],[[-4452,-672],[-672]],[[0,0],[0]],[[-19516,-616],[-616]],[[0,0],[0]],[[-40040,-224],[-224]],[[0,0],[0]],[[-46032,-28],[-28]],[[0]],[[-31808]],[[0]],[[-13468]],[[0]],[[-3416]],[[0]],[[-476]],[[0]],[[-28]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
