/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode160
import Proofs.RadenkovicGutmanD20Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-266,0],[0,0]],[[0,0],[0,0]],[[-1636,0],[0,0]],[[0,0],[0,0]],[[-5418,0],[0,0]],[[0,0],[0,0]],[[-10448,0],[0,0]],[[0,0],[0,0]],[[-11832,-18],[-18,0]],[[0,0],[0,0]],[[-7420,-144],[-144,0]],[[0,0],[0,0]],[[-1946,-396],[-396,0]],[[0,0],[0,0]],[[258,-432],[-432,0]],[[0,0],[0,0]],[[198,-162],[-162,0]],[[0],[0,0]],[[0],[0,-18]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
