/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode044
import Proofs.RadenkovicGutmanD42Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,42]],[[0,0],[0,0]],[[378,378],[378,2]],[[0,0],[0]],[[6696,1026],[1026]],[[0,0],[0]],[[29592,972],[972]],[[0,0],[0]],[[61454,380],[380]],[[0,0],[0]],[[71908,58],[58]],[[0,0],[0]],[[51000,2],[2]],[[0]],[[22474]],[[0]],[[6086]],[[0]],[[958]],[[0]],[[76]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
