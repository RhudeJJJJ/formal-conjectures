/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode160
import Proofs.RadenkovicGutmanD40Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-38],[0]],[[0,0],[0]],[[-566,0],[0,0]],[[0,0],[0,0]],[[-3516,0],[0,0]],[[0,0],[0,0]],[[-11798,0],[0,0]],[[0,0],[0,0]],[[-23168,0],[0,0]],[[0,0],[0,0]],[[-26952,-38],[-38,0]],[[0,0],[0,0]],[[-17700,-304],[-304,0]],[[0,0],[0,0]],[[-5286,-836],[-836,0]],[[0,0],[0,0]],[[198,-912],[-912,0]],[[0,0],[0,0]],[[378,-342],[-342,0]],[[0],[0,0]],[[0],[0,-38]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
