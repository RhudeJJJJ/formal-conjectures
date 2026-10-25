/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode171
import Proofs.RadenkovicGutmanD15Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[30,0],[0]],[[0,0],[0]],[[450,0],[0]],[[0,0],[0]],[[2820,0],[0]],[[0,0],[0]],[[9570,0],[0]],[[0,0],[0]],[[19080,0],[0]],[[0,0],[0]],[[22710,15],[15]],[[0,0],[0]],[[15660,105],[105]],[[0,0],[0]],[[5670,240],[240]],[[0,0],[0]],[[810,195],[195]],[[0,0],[0]],[[0,45],[45]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
