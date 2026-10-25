/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode184
import Proofs.RadenkovicGutmanD25Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[25,0],[0]],[[0,0],[0]],[[400,0],[0]],[[0,0],[0]],[[2675,0],[0]],[[0,0],[0]],[[9700,0],[0]],[[0,0],[0]],[[20700,0],[0]],[[0,0],[0]],[[26400,25],[25]],[[0,0],[0]],[[19475,175],[175]],[[0,0],[0]],[[7500,400],[400]],[[0,0],[0]],[[1125,325],[325]],[[0,0],[0]],[[0,75],[75]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
