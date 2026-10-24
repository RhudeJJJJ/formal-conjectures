/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode143
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e144 : NestedArithmetic.Expr 3 := .times e143 e121
noncomputable def p144 : NestedHorner.Poly 3 := [[[1]],[[0]],[[8]],[[0]],[[22]],[[0]],[[24]],[[0]],[[9]]]
theorem step144 : p144=NestedArithmetic.mul p143 p121 := by decide +kernel
#print axioms step144
theorem h144 : NestedArithmetic.compile e144=p144 := StagedExprCompile.compile_times e144 e143 e121 p143 p121 p144 rfl h143 h121 step144
#print axioms h144
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
