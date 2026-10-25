/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode160
import Proofs.RadenkovicGutmanD29Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-27],[0]],[[0,0],[0]],[[-401,0],[0,0]],[[0,0],[0,0]],[[-2482,0],[0,0]],[[0,0],[0,0]],[[-8289,0],[0,0]],[[0,0],[0,0]],[[-16172,0],[0,0]],[[0,0],[0,0]],[[-18636,-27],[-27,0]],[[0,0],[0,0]],[[-12046,-216],[-216,0]],[[0,0],[0,0]],[[-3449,-594],[-594,0]],[[0,0],[0,0]],[[231,-648],[-648,0]],[[0,0],[0,0]],[[279,-243],[-243,0]],[[0],[0,0]],[[0],[0,-27]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
