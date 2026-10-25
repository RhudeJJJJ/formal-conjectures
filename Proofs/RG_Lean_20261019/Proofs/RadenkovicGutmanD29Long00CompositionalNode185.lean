/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode184
import Proofs.RadenkovicGutmanD29Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[29,0],[0]],[[0,0],[0]],[[464,0],[0]],[[0,0],[0]],[[3103,0],[0]],[[0,0],[0]],[[11252,0],[0]],[[0,0],[0]],[[24012,0],[0]],[[0,0],[0]],[[30624,29],[29]],[[0,0],[0]],[[22591,203],[203]],[[0,0],[0]],[[8700,464],[464]],[[0,0],[0]],[[1305,377],[377]],[[0,0],[0]],[[0,87],[87]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
