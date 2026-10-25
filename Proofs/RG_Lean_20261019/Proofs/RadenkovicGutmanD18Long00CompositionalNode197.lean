/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode193
import Proofs.RadenkovicGutmanD18Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[120,0],[0,0]],[[0,0],[0,0]],[[1538,0],[0,0]],[[0,0],[0,0]],[[9098,0],[0,0]],[[0,0],[0,0]],[[29982,0],[0,0]],[[0,0],[0,0]],[[58752,2],[2,0]],[[0,0],[0,0]],[[69140,70],[70,0]],[[0,0],[0,0]],[[47170,440],[440,0]],[[0,0],[0,0]],[[16620,1020],[1020,0]],[[0,0],[0,0]],[[1980,918],[918,0]],[[0,0],[0,0]],[[-162,270],[270,2]],[[0],[0,0]],[[0],[0,18]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
