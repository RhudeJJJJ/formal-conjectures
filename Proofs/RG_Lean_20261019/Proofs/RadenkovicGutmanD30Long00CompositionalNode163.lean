/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode160
import Proofs.RadenkovicGutmanD30Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-416,0],[0,0]],[[0,0],[0,0]],[[-2576,0],[0,0]],[[0,0],[0,0]],[[-8608,0],[0,0]],[[0,0],[0,0]],[[-16808,0],[0,0]],[[0,0],[0,0]],[[-19392,-28],[-28,0]],[[0,0],[0,0]],[[-12560,-224],[-224,0]],[[0,0],[0,0]],[[-3616,-616],[-616,0]],[[0,0],[0,0]],[[228,-672],[-672,0]],[[0,0],[0,0]],[[288,-252],[-252,0]],[[0],[0,0]],[[0],[0,-28]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
