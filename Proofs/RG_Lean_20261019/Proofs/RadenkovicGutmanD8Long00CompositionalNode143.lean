/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode142
import Proofs.RadenkovicGutmanD8Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e143 : NestedArithmetic.Expr 3 := .times e142 e003
noncomputable def p143 : NestedHorner.Poly 3 := [[[]],[[0]],[[1]],[[0]],[[6]],[[0]],[[11]],[[0]],[[6]]]
theorem step143 : p143=NestedArithmetic.mul p142 p003 := by decide +kernel
#print axioms step143
theorem h143 : NestedArithmetic.compile e143=p143 := StagedExprCompile.compile_times e143 e142 e003 p142 p003 p143 rfl h142 h003 step143
#print axioms h143
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
