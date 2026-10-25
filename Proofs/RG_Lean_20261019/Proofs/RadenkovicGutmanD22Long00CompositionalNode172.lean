/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode171
import Proofs.RadenkovicGutmanD22Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[44,0],[0]],[[0,0],[0]],[[660,0],[0]],[[0,0],[0]],[[4136,0],[0]],[[0,0],[0]],[[14036,0],[0]],[[0,0],[0]],[[27984,0],[0]],[[0,0],[0]],[[33308,22],[22]],[[0,0],[0]],[[22968,154],[154]],[[0,0],[0]],[[8316,352],[352]],[[0,0],[0]],[[1188,286],[286]],[[0,0],[0]],[[0,66],[66]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
