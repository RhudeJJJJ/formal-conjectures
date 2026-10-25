/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode030
import Proofs.RadenkovicGutmanD9Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[18],[0]],[[0,0],[0]],[[270,0],[0]],[[0,0],[0]],[[1692,0],[0]],[[0,0],[0]],[[5742,0],[0]],[[0,0],[0]],[[11448,0],[0]],[[0,0],[0]],[[13626,9],[9]],[[0,0],[0]],[[9396,63],[63]],[[0,0],[0]],[[3402,144],[144]],[[0,0],[0]],[[486,117],[117]],[[0,0],[0]],[[0,27],[27]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
