/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode138
import Proofs.RadenkovicGutmanD32Long00CompositionalNode143
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e144 : NestedArithmetic.Expr 3 := .plus e138 e143
noncomputable def p144 : NestedHorner.Poly 3 := [[[1]],[[0]],[[8]],[[0]],[[22]],[[0]],[[24]],[[0]],[[9]]]
theorem step144 : p144=NestedHorner.add p138 p143 := by decide +kernel
#print axioms step144
theorem h144 : NestedArithmetic.compile e144=p144 := StagedExprCompile.compile_plus e144 e138 e143 p138 p143 p144 rfl h138 h143 step144
#print axioms h144
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
