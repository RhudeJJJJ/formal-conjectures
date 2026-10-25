/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode030
import Proofs.RadenkovicGutmanD10Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[20],[0]],[[0,0],[0]],[[300,0],[0]],[[0,0],[0]],[[1880,0],[0]],[[0,0],[0]],[[6380,0],[0]],[[0,0],[0]],[[12720,0],[0]],[[0,0],[0]],[[15140,10],[10]],[[0,0],[0]],[[10440,70],[70]],[[0,0],[0]],[[3780,160],[160]],[[0,0],[0]],[[540,130],[130]],[[0,0],[0]],[[0,30],[30]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
