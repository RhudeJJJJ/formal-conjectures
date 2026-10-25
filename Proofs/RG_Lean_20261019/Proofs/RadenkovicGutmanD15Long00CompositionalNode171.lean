/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode030
import Proofs.RadenkovicGutmanD15Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[30],[0]],[[0,0],[0]],[[450,0],[0]],[[0,0],[0]],[[2820,0],[0]],[[0,0],[0]],[[9570,0],[0]],[[0,0],[0]],[[19080,0],[0]],[[0,0],[0]],[[22710,15],[15]],[[0,0],[0]],[[15660,105],[105]],[[0,0],[0]],[[5670,240],[240]],[[0,0],[0]],[[810,195],[195]],[[0,0],[0]],[[0,45],[45]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
