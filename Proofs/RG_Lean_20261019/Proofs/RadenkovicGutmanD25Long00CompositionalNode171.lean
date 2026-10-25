/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode030
import Proofs.RadenkovicGutmanD25Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[50],[0]],[[0,0],[0]],[[750,0],[0]],[[0,0],[0]],[[4700,0],[0]],[[0,0],[0]],[[15950,0],[0]],[[0,0],[0]],[[31800,0],[0]],[[0,0],[0]],[[37850,25],[25]],[[0,0],[0]],[[26100,175],[175]],[[0,0],[0]],[[9450,400],[400]],[[0,0],[0]],[[1350,325],[325]],[[0,0],[0]],[[0,75],[75]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
