/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode171
import Proofs.RadenkovicGutmanD25Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[50,0],[0]],[[0,0],[0]],[[750,0],[0]],[[0,0],[0]],[[4700,0],[0]],[[0,0],[0]],[[15950,0],[0]],[[0,0],[0]],[[31800,0],[0]],[[0,0],[0]],[[37850,25],[25]],[[0,0],[0]],[[26100,175],[175]],[[0,0],[0]],[[9450,400],[400]],[[0,0],[0]],[[1350,325],[325]],[[0,0],[0]],[[0,75],[75]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
