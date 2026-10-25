/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode160
import Proofs.RadenkovicGutmanD35Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-33],[0]],[[0,0],[0]],[[-491,0],[0,0]],[[0,0],[0,0]],[[-3046,0],[0,0]],[[0,0],[0,0]],[[-10203,0],[0,0]],[[0,0],[0,0]],[[-19988,0],[0,0]],[[0,0],[0,0]],[[-23172,-33],[-33,0]],[[0,0],[0,0]],[[-15130,-264],[-264,0]],[[0,0],[0,0]],[[-4451,-726],[-726,0]],[[0,0],[0,0]],[[213,-792],[-792,0]],[[0,0],[0,0]],[[333,-297],[-297,0]],[[0],[0,0]],[[0],[0,-33]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
