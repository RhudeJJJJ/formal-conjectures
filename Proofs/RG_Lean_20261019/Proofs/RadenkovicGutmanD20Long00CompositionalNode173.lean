/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode165
import Proofs.RadenkovicGutmanD20Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-492,0],[0,0]],[[0,0],[0,0]],[[-2672,0],[0,0]],[[0,0],[0,0]],[[-7076,0],[0,0]],[[0,0],[0,0]],[[-8136,0],[0,0]],[[0,0],[0,0]],[[1776,-36],[-36,0]],[[0,0],[0,0]],[[15440,-268],[-268,0]],[[0,0],[0,0]],[[16988,-652],[-652,0]],[[0,0],[0,0]],[[8076,-544],[-544,0]],[[0,0],[0,0]],[[1476,-64],[-64,0]],[[0,0],[0,0]],[[0,60],[60,-36]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
