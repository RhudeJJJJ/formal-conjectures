/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode131
import Proofs.RadenkovicGutmanD15Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e132 : NestedArithmetic.Expr 3 := .times e131 e003
noncomputable def p132 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]]]
theorem step132 : p132=NestedArithmetic.mul p131 p003 := by decide +kernel
#print axioms step132
theorem h132 : NestedArithmetic.compile e132=p132 := StagedExprCompile.compile_times e132 e131 e003 p131 p003 p132 rfl h131 h003 step132
#print axioms h132
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
