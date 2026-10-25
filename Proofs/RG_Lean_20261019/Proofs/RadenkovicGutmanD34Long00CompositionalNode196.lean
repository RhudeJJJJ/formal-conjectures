/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode195
import Proofs.RadenkovicGutmanD34Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[136,0],[0]],[[0,0],[0]],[[2040,0],[0]],[[0,0],[0]],[[12784,0],[0]],[[0,0],[0]],[[43384,0],[0]],[[0,0],[0]],[[86496,0],[0]],[[0,0],[0]],[[102952,68],[68]],[[0,0],[0]],[[70992,476],[476]],[[0,0],[0]],[[25704,1088],[1088]],[[0,0],[0]],[[3672,884],[884]],[[0,0],[0]],[[0,204],[204]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
