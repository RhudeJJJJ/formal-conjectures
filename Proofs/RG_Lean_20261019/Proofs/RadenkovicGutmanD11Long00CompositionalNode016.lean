/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode015
import Proofs.RadenkovicGutmanD11Long00CompositionalNode012
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e016 : NestedArithmetic.Expr 3 := .times e015 e012
noncomputable def p016 : NestedHorner.Poly 3 := [[],[[]],[[3]],[[0]],[[13]],[[0]],[[16]],[[0]],[[7]],[[0]],[[1]]]
theorem step016 : p016=NestedArithmetic.mul p015 p012 := by decide +kernel
#print axioms step016
theorem h016 : NestedArithmetic.compile e016=p016 := StagedExprCompile.compile_times e016 e015 e012 p015 p012 p016 rfl h015 h012 step016
#print axioms h016
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
