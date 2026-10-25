/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode006
import Proofs.RadenkovicGutmanD9Long00CompositionalNode129
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e153 : NestedArithmetic.Expr 3 := .times e006 e129
noncomputable def p153 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step153 : p153=NestedArithmetic.mul p006 p129 := by decide +kernel
#print axioms step153
theorem h153 : NestedArithmetic.compile e153=p153 := StagedExprCompile.compile_times e153 e006 e129 p006 p129 p153 rfl h006 h129 step153
#print axioms h153
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
