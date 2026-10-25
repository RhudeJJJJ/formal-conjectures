/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode038
import Proofs.RadenkovicGutmanD29Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-27]],[[0,0],[0]],[[279,-243],[-243]],[[0,0],[0]],[[231,-648],[-648]],[[0,0],[0]],[[-3449,-594],[-594]],[[0,0],[0]],[[-12046,-216],[-216]],[[0,0],[0]],[[-18636,-27],[-27]],[[0]],[[-16172]],[[0]],[[-8289]],[[0]],[[-2482]],[[0]],[[-401]],[[0]],[[-27]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
