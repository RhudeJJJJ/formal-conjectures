/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode037
import Proofs.RadenkovicGutmanD2Long00CompositionalNode038
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e039 : NestedArithmetic.Expr 3 := .plus e037 e038
noncomputable def p039 : NestedHorner.Poly 3 := [[[0],[0,0]],[[0,0],[0]],[[36,0],[0]],[[0,0],[0]],[[312,0],[0]],[[0,0],[0]],[[1060,0],[0]],[[0,0],[0]],[[1832,0],[0]],[[0,0],[0]],[[1776,0],[0]],[[0]],[[1000]],[[0]],[[324]],[[0]],[[56]],[[0]],[[4]],[[0]],[[0]]]
theorem step039 : p039=NestedHorner.add p037 p038 := by decide +kernel
#print axioms step039
theorem h039 : NestedArithmetic.compile e039=p039 := StagedExprCompile.compile_plus e039 e037 e038 p037 p038 p039 rfl h037 h038 step039
#print axioms h039
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
