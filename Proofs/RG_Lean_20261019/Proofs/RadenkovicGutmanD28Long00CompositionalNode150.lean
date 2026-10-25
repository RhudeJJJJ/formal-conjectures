/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode145
import Proofs.RadenkovicGutmanD28Long00CompositionalNode149
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e150 : NestedArithmetic.Expr 3 := .plus e145 e149
noncomputable def p150 : NestedHorner.Poly 3 := [[[1]],[[0,0]],[[8,0]],[[0,0]],[[22,0]],[[0,0]],[[24,0]],[[0,0]],[[9,0]],[[0,0]],[[0,1]]]
theorem step150 : p150=NestedHorner.add p145 p149 := by decide +kernel
#print axioms step150
theorem h150 : NestedArithmetic.compile e150=p150 := StagedExprCompile.compile_plus e150 e145 e149 p145 p149 p150 rfl h145 h149 step150
#print axioms h150
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
