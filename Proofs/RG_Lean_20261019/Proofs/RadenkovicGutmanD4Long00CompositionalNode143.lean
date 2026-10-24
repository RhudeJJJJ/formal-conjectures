/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode137
import Proofs.RadenkovicGutmanD4Long00CompositionalNode142
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e143 : NestedArithmetic.Expr 3 := .plus e137 e142
noncomputable def p143 : NestedHorner.Poly 3 := [[[1]],[[0]],[[8]],[[0]],[[22]],[[0]],[[24]],[[0]],[[9]]]
theorem step143 : p143=NestedHorner.add p137 p142 := by decide +kernel
#print axioms step143
theorem h143 : NestedArithmetic.compile e143=p143 := StagedExprCompile.compile_plus e143 e137 e142 p137 p142 p143 rfl h137 h142 step143
#print axioms h143
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
