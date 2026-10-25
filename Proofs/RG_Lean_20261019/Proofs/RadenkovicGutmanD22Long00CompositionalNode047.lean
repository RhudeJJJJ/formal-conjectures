/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode046
import Proofs.RadenkovicGutmanD22Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e047 : NestedArithmetic.Expr 3 := .times e046 e000
noncomputable def p047 : NestedHorner.Poly 3 := [[[]],[[44]]]
theorem step047 : p047=NestedArithmetic.mul p046 p000 := by decide +kernel
#print axioms step047
theorem h047 : NestedArithmetic.compile e047=p047 := StagedExprCompile.compile_times e047 e046 e000 p046 p000 p047 rfl h046 h000 step047
#print axioms h047
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
