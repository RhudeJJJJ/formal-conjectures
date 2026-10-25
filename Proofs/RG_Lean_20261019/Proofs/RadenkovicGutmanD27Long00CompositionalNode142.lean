/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode141
import Proofs.RadenkovicGutmanD27Long00CompositionalNode136
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e142 : NestedArithmetic.Expr 3 := .times e141 e136
noncomputable def p142 : NestedHorner.Poly 3 := [[[1]],[[0]],[[6]],[[0]],[[11]],[[0]],[[6]]]
theorem step142 : p142=NestedArithmetic.mul p141 p136 := by decide +kernel
#print axioms step142
theorem h142 : NestedArithmetic.compile e142=p142 := StagedExprCompile.compile_times e142 e141 e136 p141 p136 p142 rfl h141 h136 step142
#print axioms h142
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
