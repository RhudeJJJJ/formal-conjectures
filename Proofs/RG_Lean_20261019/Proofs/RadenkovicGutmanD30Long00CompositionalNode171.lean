/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode030
import Proofs.RadenkovicGutmanD30Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[60],[0]],[[0,0],[0]],[[900,0],[0]],[[0,0],[0]],[[5640,0],[0]],[[0,0],[0]],[[19140,0],[0]],[[0,0],[0]],[[38160,0],[0]],[[0,0],[0]],[[45420,30],[30]],[[0,0],[0]],[[31320,210],[210]],[[0,0],[0]],[[11340,480],[480]],[[0,0],[0]],[[1620,390],[390]],[[0,0],[0]],[[0,90],[90]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
