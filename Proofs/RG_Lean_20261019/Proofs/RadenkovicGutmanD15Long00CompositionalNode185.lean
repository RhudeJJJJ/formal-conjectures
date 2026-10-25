/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode184
import Proofs.RadenkovicGutmanD15Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[15,0],[0]],[[0,0],[0]],[[240,0],[0]],[[0,0],[0]],[[1605,0],[0]],[[0,0],[0]],[[5820,0],[0]],[[0,0],[0]],[[12420,0],[0]],[[0,0],[0]],[[15840,15],[15]],[[0,0],[0]],[[11685,105],[105]],[[0,0],[0]],[[4500,240],[240]],[[0,0],[0]],[[675,195],[195]],[[0,0],[0]],[[0,45],[45]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
