/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode140
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e141 : NestedArithmetic.Expr 3 := .times e140 e003
noncomputable def p141 : NestedHorner.Poly 3 := [[[]],[[0]],[[1]],[[0]],[[6]],[[0]],[[11]],[[0]],[[6]]]
theorem step141 : p141=NestedArithmetic.mul p140 p003 := by decide +kernel
#print axioms step141
theorem h141 : NestedArithmetic.compile e141=p141 := StagedExprCompile.compile_times e141 e140 e003 p140 p003 p141 rfl h140 h003 step141
#print axioms h141
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
