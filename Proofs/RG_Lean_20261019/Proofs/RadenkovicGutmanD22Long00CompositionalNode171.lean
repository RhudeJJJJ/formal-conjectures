/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode030
import Proofs.RadenkovicGutmanD22Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[44],[0]],[[0,0],[0]],[[660,0],[0]],[[0,0],[0]],[[4136,0],[0]],[[0,0],[0]],[[14036,0],[0]],[[0,0],[0]],[[27984,0],[0]],[[0,0],[0]],[[33308,22],[22]],[[0,0],[0]],[[22968,154],[154]],[[0,0],[0]],[[8316,352],[352]],[[0,0],[0]],[[1188,286],[286]],[[0,0],[0]],[[0,66],[66]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
