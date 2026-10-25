/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode037
import Proofs.RadenkovicGutmanD30Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-420,0],[0,0]],[[0,0],[0,0]],[[-2632,0],[0,0]],[[0,0],[0,0]],[[-8932,0],[0,0]],[[0,0],[0,0]],[[-17808,0],[0,0]],[[0,0],[0,0]],[[-21168,-28],[-28,0]],[[0,0],[0,0]],[[-14392,-224],[-224,0]],[[0,0],[0,0]],[[-4676,-616],[-616,0]],[[0,0],[0,0]],[[-84,-672],[-672,0]],[[0,0],[0,0]],[[252,-252],[-252,0]],[[0],[0,0]],[[0],[0,-28]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
