/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode159
import Proofs.RadenkovicGutmanD30Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-420,0],[0,0]],[[0,0],[0,0]],[[-2632,0],[0,0]],[[0,0],[0,0]],[[-8932,0],[0,0]],[[0,0],[0,0]],[[-17808,0],[0,0]],[[0,0],[0,0]],[[-21168,-28],[-28,0]],[[0,0],[0,0]],[[-14392,-224],[-224,0]],[[0,0],[0,0]],[[-4676,-616],[-616,0]],[[0,0],[0,0]],[[-84,-672],[-672,0]],[[0,0],[0,0]],[[252,-252],[-252,0]],[[0],[0,0]],[[0],[0,-28]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
