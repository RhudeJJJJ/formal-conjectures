/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode038
import Proofs.RadenkovicGutmanD11Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-9]],[[0,0],[0]],[[117,-81],[-81]],[[0,0],[0]],[[285,-216],[-216]],[[0,0],[0]],[[-443,-198],[-198]],[[0,0],[0]],[[-2794,-72],[-72]],[[0,0],[0]],[[-5028,-9],[-9]],[[0]],[[-4724]],[[0]],[[-2547]],[[0]],[[-790]],[[0]],[[-131]],[[0]],[[-9]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
