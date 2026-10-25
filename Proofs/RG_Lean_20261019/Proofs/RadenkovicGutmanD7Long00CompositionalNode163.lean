/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode160
import Proofs.RadenkovicGutmanD7Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-5],[0]],[[0,0],[0]],[[-71,0],[0,0]],[[0,0],[0,0]],[[-414,0],[0,0]],[[0,0],[0,0]],[[-1271,0],[0,0]],[[0,0],[0,0]],[[-2180,0],[0,0]],[[0,0],[0,0]],[[-2004,-5],[-5,0]],[[0,0],[0,0]],[[-738,-40],[-40,0]],[[0,0],[0,0]],[[225,-110],[-110,0]],[[0,0],[0,0]],[[297,-120],[-120,0]],[[0,0],[0,0]],[[81,-45],[-45,0]],[[0],[0,0]],[[0],[0,-5]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
