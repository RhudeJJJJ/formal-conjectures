/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode188
import Proofs.RadenkovicGutmanD4Long00CompositionalNode010
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e189 : NestedArithmetic.Expr 3 := .plus e188 e010
noncomputable def p189 : NestedHorner.Poly 3 := [[[2]],[[0]],[[4]]]
theorem step189 : p189=NestedHorner.add p188 p010 := by decide +kernel
#print axioms step189
theorem h189 : NestedArithmetic.compile e189=p189 := StagedExprCompile.compile_plus e189 e188 e010 p188 p010 p189 rfl h188 h010 step189
#print axioms h189
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
