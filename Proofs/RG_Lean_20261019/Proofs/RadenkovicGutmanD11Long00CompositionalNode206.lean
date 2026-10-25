/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode203
import Proofs.RadenkovicGutmanD11Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[67,0],[0,0]],[[0,0],[0,0]],[[783,0],[0,0]],[[0,0],[0,0]],[[4658,0],[0,0]],[[0,0],[0,0]],[[16099,0],[0,0]],[[0,0],[0,0]],[[34000,2],[2,0]],[[0,0],[0,0]],[[44176,49],[49,0]],[[0,0],[0,0]],[[34262,286],[286,0]],[[0,0],[0,0]],[[14585,642],[642,0]],[[0,0],[0,0]],[[2757,568],[568,0]],[[0,0],[0,0]],[[99,165],[165,2]],[[0],[0,0]],[[0],[0,11]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
