/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode160
import Proofs.RadenkovicGutmanD8Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-86,0],[0,0]],[[0,0],[0,0]],[[-508,0],[0,0]],[[0,0],[0,0]],[[-1590,0],[0,0]],[[0,0],[0,0]],[[-2816,0],[0,0]],[[0,0],[0,0]],[[-2760,-6],[-6,0]],[[0,0],[0,0]],[[-1252,-48],[-48,0]],[[0,0],[0,0]],[[58,-132],[-132,0]],[[0,0],[0,0]],[[294,-144],[-144,0]],[[0,0],[0,0]],[[90,-54],[-54,0]],[[0],[0,0]],[[0],[0,-6]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
